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
        let mut ptrs = HashSet::new();
        Self::rec_from(&mut nodes, &mut ptrs, r1);
        Self::rec_from(&mut nodes, &mut ptrs, r2);

        Self { nodes }
    }

    fn rec_from(nodes: &mut HashSet<Rc<LNode>>, ptrs: &mut HashSet<usize>, node: Rc<LNode>) {
        let ptr = Rc::into_raw(node.clone()) as usize;
        if !ptrs.contains(&ptr) {
            ptrs.insert(ptr);
            nodes.insert(node.clone());
        }

        match node.as_ref() {
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
            let mut parents = Vec::from_iter(
                n.get_parent()
                    .iter()
                    .map(|x| x.upgrade()),
            );
            while let Some(Some(m)) = parents.pop() {
                // TODO: se `m` è una bvar istanziata, devo ciclare ANCHE sui suoi padri. Conviene utilizzare un loop piuttosto
                // che un ciclo for, ed utilizzare una coda (inizializzata ai parent di `n`) per inserire i padri.
                if m.is_bvar() && m.get_sub().is_some() {
                    let m_sub = m.get_sub().unwrap().clone();
                    let mut m_parent = m_sub
                        .get_parent()
                        .iter()
                        .map(|x| x.upgrade())
                        .collect();
                    parents.append(&mut m_parent);
                }

                let parent = m.clone().canonic().borrow().upgrade();
                match parent {
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
        let var1 = LNode::new_bvar(None, Some("x"));
        let abs1 = LNode::new_prod(var1.clone(), var1.clone());
        let app1 = LNode::new_app(abs1.clone(), abs1.clone());

        let var2 = LNode::new_bvar(None, Some("y"));
        let abs2 = LNode::new_prod(var2.clone(), var2.clone());
        let app2 = LNode::new_app(abs2.clone(), abs2.clone());
        let root1 = LNode::new_app(app1.clone(), app2.clone());

        let var3 = LNode::new_bvar(None, Some("xx"));
        let abs3 = LNode::new_prod(var3.clone(), var3.clone());
        let var4 = LNode::new_bvar(None, Some("yy"));
        let abs4 = LNode::new_prod(var4.clone(), var4.clone());

        let app3 = LNode::new_app(abs3.clone(), abs4.clone());
        let root2 = LNode::new_app(app3.clone(), app3.clone());

        // let g = LGraph::from_roots(root1.clone(), root2.clone());

        let g = LGraph::from_roots(root1.clone(), root2.clone());

        // DEBUG ONLY: prints the memory cell for each node
        println!("var1  -> {var1:p}");
        println!("abs1  -> {abs1:p}");
        println!("app1  -> {app1:p}");

        println!("var2  -> {var2:p}");
        println!("abs2  -> {abs2:p}");
        println!("app2  -> {app2:p}");
        println!("root1 -> {root1:p}");

        println!("var3  -> {var3:p}");
        println!("abs3  -> {abs3:p}");
        println!("var4  -> {var4:p}");
        println!("abs4  -> {abs4:p}");

        println!("app3  -> {app3:p}");
        println!("root2 -> {root2:p}");
        // g.nodes.iter().for_each(|n| println!("{:?}, {0:p}", n));

        println!("{}", g.nodes.len());

        let check_res = g.blind_check();
        assert!(check_res.is_ok(), "{}", check_res.err().unwrap());
        println!("\nCANONIC EDGES");
        g.nodes.iter().for_each(|n| {
            println!(
                "{:p} -> {:p}",
                n.clone(),
                n.canonic().borrow().upgrade().expect("Error")
            )
        });

        assert!(g.var_check(), "The query is not a sharing equivalence.");
    }
}
