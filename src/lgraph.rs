use std::{
    fmt::Debug,
    rc::Rc,
};

use crate::lnode::*;
use LNode::*;

/// Structure that defines a Lambda-Graph (see [this](https://arxiv.org/pdf/1907.06101.pdf)).
#[derive(Clone, Debug)]
pub struct LGraph {
    nodes: Vec<Rc<LNode>>,
}

#[allow(dead_code)]
impl LGraph {
    /// Returns an empty LGraph.
    pub fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    /// Returns an LGraph that has `v` as nodes.
    pub fn from(v: Vec<Rc<LNode>>) -> Self {
        Self { nodes: v }
    }

    /// Adds `node` to the nodes of the graph.
    pub fn add_node(&mut self, node: Rc<LNode>) {
        self.nodes.push(node);
    }

    fn var_nodes(&self) -> Vec<Rc<LNode>> {
        self.nodes
            .iter()
            .filter(|x| x.is_bvar() || x.is_var())
            .map(|x| x.clone())
            .collect()
    }

    /// Function that populates the entries of the current state. It uses two internal functions, namely
    /// - `build_equivalence_class`: build the equivalence class for a given node.
    /// - `enqueue_and_propagate`: creates a queue of the homogeneous node in an equivalence class.
    /// On callback termination, it is expected that the field `undir` contains pairs `(u, v)` such that `u ~ v` where
    /// `~` is the equivalence relation described in the [paper of reference](https://arxiv.org/pdf/1907.06101.pdf)
    pub fn blind_check(&self) -> Result<(), String> {
        for n in self.nodes.iter() {
            // if canonic(n) is undefined
            if n.canonic().borrow().clone().upgrade().is_none() {
                if let Err(e) = self.build_equivalence_class(n.clone()) {
                    return Err(e);
                }
            }
        }

        Ok(())
    }

    fn build_equivalence_class(&self, c: Rc<LNode>) -> Result<(), String> {
        *c.canonic().borrow_mut() = Rc::downgrade(&c);
        *c.building().borrow_mut() = true;
        c.queue().borrow_mut().push_back(Rc::downgrade(&c));

        loop {
            let n = c.queue().borrow_mut().pop_front();
            if n.is_none() {
                break;
            }
            let n = n.unwrap().upgrade().unwrap();

            // For every parent m of n ...
            for m in n.get_parent().iter().map(|x| x.upgrade()) {
                if let Some(m) = m {
                    match m.canonic().borrow().upgrade() {
                        None => {
                            if let Err(e) = self.build_equivalence_class(m.clone()) {
                                return Err(e);
                            }
                        }
                        Some(c1) => {
                            if *c1.building().borrow() {
                                return Err(String::from("Error: Parent still building"));
                            }
                        }
                    }
                }
            }

            // For every ~neighbour m of n ...
            for m in n.undir().borrow().iter() {
                let m = m.upgrade().unwrap();
                let m1 = m.clone().canonic().borrow().upgrade();
                match m1 {
                    None => {
                        if let Err(e) = self.enqueue_and_propagate(m.clone(), c.clone()) {
                            return Err(e);
                        }

                        // If `m` is not dropped, `borrowMut` error rises since `m` is borrowed as mut more than once
                        drop(m);
                    }
                    Some(c1) => {
                        if c1 != c {
                            return Err(String::from(
                                "Error: found two representative nodes for the same class.",
                            ));
                        }
                    }
                }
            }
        }

        *c.building().borrow_mut() = false;

        Ok(())
    }

    fn enqueue_and_propagate(&self, m: Rc<LNode>, c: Rc<LNode>) -> Result<(), String> {
        match (m.as_ref(), c.as_ref()) {
            (
                Abs {
                    body: b1,
                    parent: _,
                    undir: _,
                    canonic: _,
                    building: _,
                    queue: _,
                },
                Abs {
                    body: b2,
                    parent: _,
                    undir: _,
                    canonic: _,
                    building: _,
                    queue: _,
                },
            ) => {
                b1.undir().borrow_mut().push(Rc::downgrade(&b2));
                b2.undir().borrow_mut().push(Rc::downgrade(&b1));
            }
            (
                App {
                    left: l1,
                    right: r1,
                    parent: _,
                    undir: _,
                    canonic: _,
                    building: _,
                    queue: _,
                },
                App {
                    left: l2,
                    right: r2,
                    parent: _,
                    undir: _,
                    canonic: _,
                    building: _,
                    queue: _,
                },
            ) => {
                l1.undir().borrow_mut().push(Rc::downgrade(&l2));
                l2.undir().borrow_mut().push(Rc::downgrade(&l1));

                r1.undir().borrow_mut().push(Rc::downgrade(&r2));
                r2.undir().borrow_mut().push(Rc::downgrade(&r1));
            }
            (
                Var {
                    parent: _,
                    undir: _,
                    canonic: _,
                    building: _,
                    queue: _,
                },
                Var {
                    parent: _,
                    undir: _,
                    canonic: _,
                    building: _,
                    queue: _,
                },
            ) => (),
            (
                BVar {
                    binder: _,
                    parent: _,
                    undir: _,
                    canonic: _,
                    building: _,
                    queue: _,
                },
                BVar {
                    binder: _,
                    parent: _,
                    undir: _,
                    canonic: _,
                    building: _,
                    queue: _,
                },
            ) => (),
            (_, _) => {
                return Err(String::from(
                    "Error: tried to compare two different kind of nodes.",
                ));
            }
        }

        *m.canonic().borrow_mut() = Rc::downgrade(&c);
        c.queue().borrow_mut().push_back(Rc::downgrade(&m));

        Ok(())
    }

    /// Function that check if the `var` nodes of the graph satisfy the conditions for a sharing equivalence.
    /// Returns `true` if the conditions are met, `false` otherwise
    pub fn var_check(&self) -> bool {
        for v in self.var_nodes() {
            let w = v.canonic().borrow().upgrade().unwrap();
            if v != w {
                if v.is_var() || w.is_var() {
                    return false;
                }
                match (v.as_ref(), w.as_ref()) {
                    (
                        BVar {
                            binder: b1,
                            parent: _,
                            undir: _,
                            canonic: _,
                            building: _,
                            queue: _,
                        },
                        BVar {
                            binder: b2,
                            parent: _,
                            undir: _,
                            canonic: _,
                            building: _,
                            queue: _,
                        },
                    ) => {
                        let b1_canonic = b1
                            .borrow()
                            .upgrade()
                            .unwrap()
                            .canonic()
                            .borrow()
                            .upgrade()
                            .unwrap();
                        let b2_canonic = b2
                            .borrow()
                            .upgrade()
                            .unwrap()
                            .canonic()
                            .borrow()
                            .upgrade()
                            .unwrap();
                        if b1_canonic != b2_canonic {
                            return false;
                        }
                    }

                    (_, _) => (),
                }
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, rc::Weak};

    use super::*;
    #[test]
    fn test() {
        let var1 = Rc::new(BVar {
            binder: RefCell::new(Weak::new()),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });
        let abs1 = Rc::new(Abs {
            body: var1.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });
        let app1 = Rc::new(App {
            left: abs1.clone(),
            right: abs1.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });

        let var2 = Rc::new(BVar {
            binder: RefCell::new(Weak::new()),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });
        let abs2 = Rc::new(Abs {
            body: var2.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });
        let app2 = Rc::new(App {
            left: abs2.clone(),
            right: abs2.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });
        let root1 = Rc::new(App {
            left: app1.clone(),
            right: app2.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });

        let var3 = Rc::new(BVar {
            binder: RefCell::new(Weak::new()),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });
        let abs3 = Rc::new(Abs {
            body: var3.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });
        let var4 = Rc::new(BVar {
            binder: RefCell::new(Weak::new()),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });
        let abs4 = Rc::new(Abs {
            body: var4.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });
        let app3 = Rc::new(App {
            left: abs3.clone(),
            right: abs4.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });
        let root2 = Rc::new(App {
            left: app3.clone(),
            right: app3.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });

        root1.undir().borrow_mut().push(Rc::downgrade(&root2));
        root2.undir().borrow_mut().push(Rc::downgrade(&root1));

        // Setting up the parents.
        var1.add_parent(abs1.clone());
        abs1.add_parent(app1.clone());
        app1.add_parent(root1.clone());
        var2.add_parent(abs2.clone());
        abs2.add_parent(app2.clone());
        app2.add_parent(root1.clone());
        var3.add_parent(abs3.clone());
        abs3.add_parent(app3.clone());
        var4.add_parent(abs4.clone());
        abs4.add_parent(app3.clone());
        app3.add_parent(root2.clone());

        // Bound the variable nodes.
        var4.bind_to(abs4.clone());
        var3.bind_to(abs3.clone());
        var2.bind_to(abs2.clone());
        var1.bind_to(abs1.clone());

        let g = LGraph::from(vec![
            root1.clone(),
            app1.clone(),
            abs1.clone(),
            var1.clone(),
            app2.clone(),
            abs2.clone(),
            var2.clone(),
            root2.clone(),
            app3.clone(),
            abs3.clone(),
            var3.clone(),
        ]);

        // DEBUG ONLY: prints the memory cell for each node
        g.nodes.iter().for_each(|n| println!("{:?}", n));

        let check_res = g.blind_check();
        assert!(check_res.is_ok(), "{}", check_res.err().unwrap());
        println!("\nCANONIC EDGES");
        g.nodes
            .iter()
            .for_each(|n| println!("{:?} -> {:?}", n, n.canonic().borrow().upgrade()));

        assert!(g.var_check(), "The query is not a sharing equivalence.");
    }
}
