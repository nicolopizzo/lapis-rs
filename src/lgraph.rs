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
        let mut nodes = HashSet::new();
        let mut ptrs = HashSet::new();
        Self::rec_from(&mut nodes, &mut ptrs, r1.clone());
        Self::rec_from(&mut nodes, &mut ptrs, r2.clone());

        // Creo un arco tra le due radici
        r1.add_undir(&r2);
        r2.add_undir(&r1);


        Self { nodes }
    }

    fn rec_from(nodes: &mut HashSet<Rc<LNode>>, ptrs: &mut HashSet<usize>, node: Rc<LNode>) {
        let ptr = Rc::into_raw(node.clone()) as usize;
        if !ptrs.contains(&ptr) {
            ptrs.insert(ptr);
            nodes.insert(node.clone());
        }

        // Resettare il nodo.
        node.reset();

        match &*node {
            App { left, right, .. } => {
                let left_ptr = Rc::into_raw(left.clone()) as usize;
                if !ptrs.contains(&left_ptr) {
                    ptrs.insert(left_ptr);
                    nodes.insert(left.clone());
                    Self::rec_from(nodes, ptrs, left.clone());
                }

                let right_ptr = Rc::into_raw(right.clone()) as usize;
                if !ptrs.contains(&right_ptr) {
                    ptrs.insert(right_ptr);
                    nodes.insert(right.clone());
                    Self::rec_from(nodes, ptrs, right.clone());
                }
            }
            Prod { bvar, body, .. } => {
                let bvar_ptr = Rc::into_raw(bvar.clone()) as usize;
                if !ptrs.contains(&bvar_ptr) {
                    ptrs.insert(bvar_ptr);
                    nodes.insert(bvar.clone());
                    Self::rec_from(nodes, ptrs, bvar.clone());
                }

                let body_ptr = Rc::into_raw(body.clone()) as usize;
                if !ptrs.contains(&body_ptr) {
                    ptrs.insert(body_ptr);
                    nodes.insert(body.clone());
                    Self::rec_from(nodes, ptrs, body.clone());
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
        for n in &self.nodes {
            let c_n = n.canonic();
            if c_n.upgrade().is_none() {
                self.build_equivalence_class(n.clone())?;
            } else {
            }
        }

        Ok(())
    }

    fn build_equivalence_class(&self, c: Rc<LNode>) -> Result<(), String> {
        c.set_canonic(Rc::downgrade(&c));
        c.set_building(true);
        c.push_queue(&c);

        loop {
            let n = c.pop_queue();
            if n.is_none() {
                break;
            }
            let n = n.unwrap().upgrade().unwrap();

            // If n is a `BVar` and is instatiated, use it instead of the theoretical variable. The following
            // snippet is equal to the used code, but `n` should be

            // Check parents of n. If n is a `BVar` and is instatiated, use the substitution.
            let mut parents: Vec<_> = n.get_parent().iter().map(|x| x.upgrade()).collect();
            while let Some(Some(m)) = parents.pop() {
                // TODO: se `m` è una bvar istanziata, devo ciclare ANCHE sui suoi padri. Conviene utilizzare un loop piuttosto
                // che un ciclo for, ed utilizzare una coda (inizializzata ai parent di `n`) per inserire i padri.
                if m.is_bvar() && m.get_sub().is_some() {
                    let m_sub = m.get_sub().unwrap().clone();
                    let mut m_parent = m_sub.get_parent().iter().map(|x| x.upgrade()).collect();
                    parents.append(&mut m_parent);
                }

                // let parent = m.clone().canonic().borrow().upgrade();
                let parent = m.canonic().upgrade();
                match parent {
                    None => {
                        if let Err(e) = self.build_equivalence_class(m.clone()) {
                            return Err(e);
                        }
                    }
                    Some(c1) => {
                        if c1.building() {
                            return Err(String::from("Error: Parent still building"));
                        }
                    }
                }
            }

            // For every ~neighbour m of n ...
            for m in n.undir().iter() {
                let m = m.upgrade().unwrap();
                let m1 = m.canonic().upgrade();
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

    fn enqueue_and_propagate(&self, m: Rc<LNode>, c: Rc<LNode>) -> Result<(), String> {
        match (&*m, &*c) {
            (Prod { body: b1, .. }, Prod { body: b2, .. })
            | (Abs { body: b1, .. }, Abs { body: b2, .. }) => {
                b1.add_undir(&b2);
                b2.add_undir(&b1);
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
                l1.add_undir(&l2);
                l2.add_undir(&l1);

                r1.add_undir(&r2);
                r2.add_undir(&r1);
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
        c.push_queue(&m);

        Ok(())
    }

    /// Function that check if the `var` nodes of the graph satisfy the conditions for a sharing equivalence.
    /// Returns `true` if the conditions are met, `false` otherwise
    pub fn var_check(&self) -> bool {
        for v in self.var_nodes() {
            let w = v.canonic().upgrade().unwrap();
            if v != w {
                if v.is_var() || w.is_var() {
                    return false;
                }
                match (&*v, &*w) {
                    (BVar { binder: b1, .. }, BVar { binder: b2, .. }) => {
                        let b1 = b1.borrow().clone().upgrade();
                        let b2 = b2.borrow().clone().upgrade();
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

                            _ => (),
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

        let g = LGraph::from_roots(root1.clone(), root2.clone());

        let check_res = g.blind_check();
        assert!(check_res.is_ok(), "{}", check_res.err().unwrap());
        g.nodes.iter().for_each(|n| {
            println!(
                "{:?} -> {:?}",
                n.clone(),
                n.canonic().upgrade().expect("Error")
            )
        });

        assert!(g.var_check(), "The query is not a sharing equivalence.");
    }
}
