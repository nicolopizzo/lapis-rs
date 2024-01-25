use std::{collections::HashSet, fmt::Debug, rc::Rc, vec};

use crate::{debug, lnode::*};
use log::info;
use LNode::*;

/// Structure that defines a Lambda-Graph (see [this](https://arxiv.org/pdf/1907.06101.pdf)).
#[derive(Clone, Debug)]
pub struct LGraph<'a> {
    nodes: HashSet<&'a Rc<LNode>>,
}

impl<'a, 'b: 'a> LGraph<'a> {
    /// Returns an empty LGraph.
    pub fn new() -> Self {
        Self {
            nodes: HashSet::new(),
        }
    }

    /// Returns an LGraph that creates an edge between `r2` and `r1` and contains the children
    /// of both nodes.
    pub fn from_roots(r1: &'b Rc<LNode>, r2: &'b Rc<LNode>) -> Self {
        let mut nodes = HashSet::new();
        let mut ptrs = HashSet::new();
        Self::rec_from(&mut nodes, &mut ptrs, r1);
        Self::rec_from(&mut nodes, &mut ptrs, r2);

        // Creo un arco tra le due radici
        r1.add_undir(r2);
        r2.add_undir(r1);

        Self { nodes }
    }

    fn rec_insert(
        term: &'b Rc<LNode>,
        ptrs: &mut HashSet<usize>,
        nodes: &mut HashSet<&'a Rc<LNode>>,
    ) {
        let left_ptr = Rc::into_raw(term.clone()) as usize;
        if !ptrs.contains(&left_ptr) {
            ptrs.insert(left_ptr);
            nodes.insert(term);
            Self::rec_from(nodes, ptrs, term);
        }
    }

    fn rec_from(
        nodes: &mut HashSet<&'a Rc<LNode>>,
        ptrs: &mut HashSet<usize>,
        node: &'b Rc<LNode>,
    ) {
        Self::rec_insert(node, ptrs, nodes);

        // Resettare il nodo.
        node.reset();

        match &**node {
            App { left, right, .. } => {
                Self::rec_insert(left, ptrs, nodes);
                Self::rec_insert(right, ptrs, nodes);
            }
            Prod { bvar, body, .. } | Abs { bvar, body, .. } => {
                Self::rec_insert(bvar, ptrs, nodes);
                Self::rec_insert(body, ptrs, nodes);
            }
            _ => (),
        }
    }

    /// Adds `node` to the nodes of the graph.
    pub fn add_node(&mut self, node: &'b Rc<LNode>) {
        self.nodes.insert(node);
    }

    fn var_nodes(&self) -> Vec<&Rc<LNode>> {
        self.nodes
            .iter()
            .copied()
            .filter(|x| x.is_var())
            .collect()
    }

    /// Function that populates the entries of the current state. It uses two internal functions, namely
    /// - `build_equivalence_class`: build the equivalence class for a given node.
    /// - `enqueue_and_propagate`: creates a queue of the homogeneous node in an equivalence class.
    /// On callback termination, it is expected that the field `undir` contains pairs `(u, v)` such that `u ~ v` where
    /// `~` is the equivalence relation described in the [paper of reference](https://arxiv.org/pdf/1907.06101.pdf)
    pub fn blind_check(&self) -> Result<(), String> {
        for n in &self.nodes {
            let c_n = n.canonic();

            // Invariant: canonic is set if it is Some(x) after upgrade.
            if c_n.upgrade().is_none() {
                self.build_equivalence_class(n)?;
            }
        }

        Ok(())
    }

    fn build_equivalence_class(&self, c: &Rc<LNode>) -> Result<(), String> {
        c.set_canonic(Rc::downgrade(c));
        c.set_building(true);
        c.push_queue(c);

        loop {
            let n = c.pop_queue();
            if n.is_none() {
                break;
            }
            let n = n.unwrap().upgrade().unwrap();

            // Check parents of n. If n is a `Var` and is instatiated, use the substitution.
            let mut parents: Vec<Option<Rc<LNode>>> =
                n.get_parent().iter().map(|x| x.upgrade()).collect();
            while let Some(Some(m)) = parents.pop() {
                // Se `m` è una bvar istanziata, devo ciclare ANCHE sui suoi padri. Conviene utilizzare un loop piuttosto
                // che un ciclo for, ed utilizzare una coda (inizializzata ai parent di `n`) per inserire i padri.
                if m.is_var() && m.get_sub().is_some() {
                    let m_sub = &m.get_sub().unwrap();
                    let m_parent: Vec<_> = m_sub.get_parent().iter().map(|x| x.upgrade()).collect();
                    parents.extend(m_parent);
                }

                let c_parent = m.canonic().upgrade();
                match c_parent {
                    None => self.build_equivalence_class(&m)?,
                    Some(c1) => {
                        if c1.building() {
                            return Err(String::from("Error: Parent still building"));
                        }
                    }
                }
            }

            // FIXME: possibile fix: devo andare sui binder...?

            // For every ~neighbour m of n ...
            for m in n.undir().iter() {
                let m = m.upgrade().unwrap();
                let m1 = m.canonic().upgrade();
                match m1 {
                    None => self.enqueue_and_propagate(&m, c)?,
                    Some(c1) => {
                        let cc = c.clone();
                        if c1 != cc {
                            return Err(format!(
                                "Error: found two representative nodes for the same class. {:?} != {:?} ({0:p} != {1:p})", c1, cc
                            ));
                        }
                    }
                }
            }
        }

        c.set_building(false);

        Ok(())
    }

    fn enqueue_and_propagate(&self, m: &Rc<LNode>, c: &Rc<LNode>) -> Result<(), String> {
        match (&**m, &**c) {
            (Prod { body: b1, .. }, Prod { body: b2, .. })
            | (Abs { body: b1, .. }, Abs { body: b2, .. }) => {
                b1.add_undir(b2);
                b2.add_undir(b1);
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
                l1.add_undir(l2);
                l2.add_undir(l1);

                r1.add_undir(r2);
                r2.add_undir(r1);
            }
            (Var { .. }, Var { .. }) => {}
            (
                Var {
                    subs_to, is_meta, ..
                },
                _,
            ) => {
                let sub = &mut *subs_to.borrow_mut();
                if let Some(sub) = sub {
                    return self.enqueue_and_propagate(sub, c);
                } else if *is_meta {
                    *sub = Some(c.clone());
                } else {
                    return Err(String::from(
                        "Error: tried to compare two different kind of nodes.",
                    ));
                }
            }
            (
                _,
                Var {
                    subs_to, is_meta, ..
                },
            ) => {
                // TODO: Se la prima `Var` ha una sostituzione, non per forza la sto confrontando con una Var
                // Devo quindi effettuare `enqueue_and_propagate` della sostituzione con v.
                let sub = &mut *subs_to.borrow_mut();
                if let Some(sub) = sub {
                    return self.enqueue_and_propagate(m, sub);
                } else if *is_meta {
                    *sub = Some(m.clone());
                } else {
                    return Err(String::from(
                        "Error: tried to compare two different kind of nodes.",
                    ));
                }
            }
            (_, _) => {
                return Err(format!(
                    "Error: tried to compare two different kind of nodes. {:?} <=> {:?}",
                    m, c
                ));
            }
        }

        m.set_canonic(Rc::downgrade(c));
        c.push_queue(m);

        Ok(())
    }

    /// Function that check if the `var` nodes of the graph satisfy the conditions for a sharing equivalence.
    /// Returns `true` if the conditions are met, `false` otherwise
    pub fn var_check(&self) -> bool {
        for v in self.var_nodes() {
            let w = v.canonic().upgrade().unwrap();
            if *v != w {
                if v.is_var() || w.is_var() {
                    return false;
                }
                if let (Var { binder: b1, .. }, Var { binder: b2, .. }) = (&**v, &*w) {
                    let b1 = &b1.borrow().upgrade();
                    let b2 = &b2.borrow().upgrade();
                    match (&b1, &b2) {
                        // If both bvars have a binder check their canonic form.
                        (Some(b1), Some(b2)) => {
                            let canonic_b1 = b1.canonic().upgrade();
                            let canonic_b2 = b2.canonic().upgrade();

                            // If the found canonic do not match, the var_check fails.
                            if canonic_b1 != canonic_b2 {
                                return false;
                            }
                        }

                        (None, None) => (),
                        _ => {
                            return false;
                        }
                    }
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

    use super::*;
    #[test]
    fn test() {
        let var1 = LNode::new_bvar(None, Some("x"));
        let abs1 = LNode::new_abs(var1.clone(), var1.clone());
        let app1 = LNode::new_app(abs1.clone(), abs1.clone());

        let var2 = LNode::new_bvar(None, Some("y"));
        let abs2 = LNode::new_abs(var2.clone(), var2.clone());
        let app2 = LNode::new_app(abs2.clone(), abs2.clone());
        let root1 = LNode::new_app(app1.clone(), app2.clone());

        let var3 = LNode::new_bvar(None, Some("xx"));
        let abs3 = LNode::new_abs(var3.clone(), var3.clone());
        let var4 = LNode::new_bvar(None, Some("yy"));
        let abs4 = LNode::new_abs(var4.clone(), var4.clone());

        let app3 = LNode::new_app(abs3.clone(), abs4.clone());
        let root2 = LNode::new_app(app3.clone(), app3.clone());

        let g = LGraph::from_roots(&root1, &root2);
        println!("{:?}", g.nodes.len());
        let check_res = g.blind_check();
        assert!(check_res.is_ok(), "{}", check_res.err().unwrap());
        g.nodes.iter().for_each(|n| {
            println!(
                "[ {:?} ] -> [ {:?} ]",
                n,
                n.canonic().upgrade().expect("Error")
            )
        });

        assert!(g.var_check(), "The query is not a sharing equivalence.");
    }
}
