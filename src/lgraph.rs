use std::{collections::HashSet, fmt::Debug, rc::Rc, vec};

use crate::lnode::*;
use LNode::*;

/// Structure that defines a Lambda-Graph (see [this](https://arxiv.org/pdf/1907.06101.pdf)).
#[derive(Clone, Debug)]
pub struct LGraph {
    nodes: HashSet<Rc<LNode>>,
}

impl LGraph {
    /// Returns an empty LGraph.
    pub fn new() -> Self {
        Self {
            nodes: HashSet::new(),
        }
    }

    /// Returns an LGraph that creates an edge between `r2` and `r1` and contains the children
    /// of both nodes.
    pub fn from_roots(r1: Rc<LNode>, r2: Rc<LNode>) -> Self {
        // Creo un arco tra le due radici
        r1.undir().borrow_mut().push(Rc::downgrade(&r2));
        r2.undir().borrow_mut().push(Rc::downgrade(&r1));

        let mut nodes = HashSet::new();

        Self::rec_from(&mut nodes, r1);
        Self::rec_from(&mut nodes, r2);

        Self { nodes }
    }

    fn rec_from(nodes: &mut HashSet<Rc<LNode>>, node: Rc<LNode>) {
        if !nodes.contains(&node) {
            nodes.insert(node.clone());
        }

        match node.as_ref() {
            App { left, right, .. } => {
                if !nodes.contains(left) {
                    nodes.insert(left.clone());
                    Self::rec_from(nodes, left.clone());
                }

                if !nodes.contains(right) {
                    nodes.insert(right.clone());
                    Self::rec_from(nodes, right.clone());
                }
            }
            Prod { bvar, body, .. } => {
                if !nodes.contains(bvar) {
                    nodes.insert(bvar.clone());
                    Self::rec_from(nodes, bvar.clone());
                }

                if !nodes.contains(body) {
                    nodes.insert(body.clone());
                    Self::rec_from(nodes, body.clone());
                }
            }
            _ => (),
        }
    }

    /// Adds `node` to the nodes of the graph.
    pub fn add_node(&mut self, node: Rc<LNode>) {
        self.nodes.insert(node);
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
        c.set_canonic(Rc::downgrade(&c));
        c.set_building(true);
        c.queue().borrow_mut().push_back(Rc::downgrade(&c));

        loop {
            let n = c.queue().borrow_mut().pop_front();
            if n.is_none() {
                break;
            }
            let n = n.unwrap().upgrade().unwrap();

            // If n is a `BVar` and is instatiated, use it instead of the theoretical variable. The following
            // snippet is equal to the used code, but `n` should be

            // Check parents of n. If n is a `BVar` and is instatiated, use the substitution.
            if n.is_bvar() && n.get_sub().is_some() {
                let n = n.get_sub().unwrap();
                if let Some(error) = self.check_parents(n.clone()) {
                    return error;
                }
            } else {
                if let Some(error) = self.check_parents(n.clone()) {
                    return error;
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

        c.set_building(false);

        Ok(())
    }

    fn check_parents(&self, n: Rc<LNode>) -> Option<Result<(), String>> {
        for m in n.get_parent().iter().map(|x| x.upgrade()) {
            if let Some(m) = m {
                let parent = m.clone().canonic().borrow().upgrade();
                match parent {
                    None => {
                        if let Err(e) = self.build_equivalence_class(m.clone()) {
                            return Some(Err(e));
                        }
                    }
                    Some(c1) => {
                        if *c1.building().borrow() {
                            return Some(Err(String::from("Error: Parent still building")));
                        }
                    }
                }
            }
        }
        None
    }

    fn enqueue_and_propagate(&self, m: Rc<LNode>, c: Rc<LNode>) -> Result<(), String> {
        match (m.as_ref(), c.as_ref()) {
            (Prod { body: b1, .. }, Prod { body: b2, .. })
            | (Abs { body: b1, .. }, Abs { body: b2, .. }) => {
                b1.undir().borrow_mut().push(Rc::downgrade(&b2));
                b2.undir().borrow_mut().push(Rc::downgrade(&b1));
            }
            (
                App {
                    left: l1,
                    right: r1,
                    ..
                },
                App {
                    left: l2,
                    right: r2,
                    ..
                },
            ) => {
                l1.undir().borrow_mut().push(Rc::downgrade(&l2));
                l2.undir().borrow_mut().push(Rc::downgrade(&l1));

                r1.undir().borrow_mut().push(Rc::downgrade(&r2));
                r2.undir().borrow_mut().push(Rc::downgrade(&r1));
            }
            (Var { .. }, Var { .. }) => (),
            (BVar { .. }, BVar { .. }) => (),
            (BVar { subs_to, .. }, _) => {
                if let Some(sub) = subs_to.borrow().clone() {
                    return self.enqueue_and_propagate(sub, c);
                } else {
                    return Err(String::from(
                        "Error: tried to compare two different kind of nodes.",
                    ));
                }
            }
            (_, BVar { subs_to, .. }) => {
                // TODO: Se la prima `BVar` ha una sostituzione, non per forza la sto confrontando con una BVar
                // Devo quindi effettuare `enqueue_and_propagate` della sostituzione con v.
                if let Some(sub) = subs_to.borrow().clone() {
                    return self.enqueue_and_propagate(sub, m);
                } else {
                    return Err(String::from(
                        "Error: tried to compare two different kind of nodes.",
                    ));
                }
            }
            (_, _) => {
                return Err(String::from(
                    "Error: tried to compare two different kind of nodes.",
                ));
            }
        }

        m.set_canonic(Rc::downgrade(&c));
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
                    (BVar { binder: b1, .. }, BVar { binder: b2, .. }) => {
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
    use std::{
        cell::RefCell,
        collections::HashMap,
        hash,
        rc::{Rc, Weak},
    };

    use crate::parser::print_context;

    use super::*;
    #[test]
    fn test() {
        let var1 = Rc::new(LNode::new_bvar(None));
        let abs1 = Rc::new(LNode::new_prod(var1.clone(), var1.clone()));
        let app1 = Rc::new(LNode::new_app(abs1.clone(), abs1.clone()));

        let var2 = Rc::new(LNode::new_bvar(None));
        let abs2 = Rc::new(LNode::new_prod(var2.clone(), var2.clone()));
        let app2 = Rc::new(LNode::new_app(abs2.clone(), abs2.clone()));
        let root1 = Rc::new(LNode::new_app(app1.clone(), app2.clone()));

        let var3 = Rc::new(LNode::new_bvar(None));
        let abs3 = Rc::new(LNode::new_prod(var3.clone(), var3.clone()));
        let var4 = Rc::new(LNode::new_bvar(None));
        let abs4 = Rc::new(LNode::new_prod(var4.clone(), var4.clone()));

        let app3 = Rc::new(LNode::new_app(abs3.clone(), abs4.clone()));
        let root2 = Rc::new(LNode::new_app(app3.clone(), app3.clone()));

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

        // let g = LGraph::from_roots(root1.clone(), root2.clone());

        let g = LGraph::from_roots(root1.clone(), root2.clone());

        // DEBUG ONLY: prints the memory cell for each node
        // g.nodes.iter().for_each(|n| println!("{:?}, {0:p}", n));

        let check_res = g.blind_check();
        assert!(check_res.is_ok(), "{}", check_res.err().unwrap());
        println!("\nCANONIC EDGES");
        g.nodes
            .iter()
            .for_each(|n| println!("{:?} -> {:?}", n, n.canonic().borrow().upgrade()));

        assert!(g.var_check(), "The query is not a sharing equivalence.");
    }
}
