use std::{
    cell::RefCell,
    collections::VecDeque,
    fmt::Debug,
    rc::{Rc, Weak},
};
use LNode::*;

/// Enum representing a lambda node. Such node can have three forms:
/// - Application: an application node has two children
/// - Abstraction: an abstraction node has one child
/// - Variable: this kind of node can represent bound and unbound variables.
#[derive(Clone)]
pub enum LNode {
    App(Rc<Self>, Rc<Self>, RefCell<Vec<Weak<Self>>>),
    Abs(Rc<Self>, RefCell<Vec<Weak<Self>>>),
    BVar(RefCell<Weak<Self>>, RefCell<Vec<Weak<Self>>>),
    Var(RefCell<Vec<Weak<Self>>>),
}

/// Implementing runtime equality for LNode.
impl PartialEq for LNode {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }

    fn ne(&self, other: &Self) -> bool {
        !Self::eq(self, other)
    }
}

impl Debug for LNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Abs(_, _) => f.write_fmt(format_args!("Abs: {:p}", self)),
            App(_, _, _) => f.write_fmt(format_args!("App: {:p}", self)),
            BVar(_, _) => f.write_fmt(format_args!("Var: {:p}", self)),
            Var(_) => f.write_fmt(format_args!("Var: {:p}", self)),
        }
    }
}

impl LNode {
    /// Modifies the current node parent pointer with `p`. It has not a public
    fn add_parent(&self, p: Rc<LNode>) {
        let parent = Rc::downgrade(&p);
        match &*self {
            App(_, _, p) => p.borrow_mut().push(parent),
            Abs(_, p) => p.borrow_mut().push(parent),
            BVar(_, p) => p.borrow_mut().push(parent),
            Var(p) => p.borrow_mut().push(parent),
        }
    }

    /// Returns the reference to the parent of the current node.
    pub fn get_parent(&self) -> Vec<Weak<Self>> {
        let p = match self {
            App(_, _, p) => p,
            Abs(_, p) => p,
            BVar(_, p) => p,
            Var(p) => p,
        };

        let p = p.borrow();
        let p = p.clone();
        p
    }

    pub fn add_abs(&self, abs: Rc<LNode>) {
        let abs = Rc::downgrade(&abs);
        match &*self {
            BVar(x, _) => *x.borrow_mut() = abs,
            _ => (),
        }
    }
}
/// Structure that defines a Lambda-Graph (see [this](https://arxiv.org/pdf/1907.06101.pdf)).
#[derive(Clone, Debug)]
pub struct LGraph {
    nodes: Vec<Rc<LNode>>,
}

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
}

/// Structure holding the information to build the equivalence classes over a lambda graph.
#[derive(Clone, Debug)]
pub struct State {
    g: LGraph,
    undir: Vec<(Rc<LNode>, Rc<LNode>)>,   //undirected edges
    canonic: Vec<(Rc<LNode>, Rc<LNode>)>, // canonic edges
    building: Vec<(Rc<LNode>, bool)>,
    queue: Vec<(Rc<LNode>, VecDeque<Rc<LNode>>)>,
}

impl State {
    /// Returns a new state with an initial edge `(u, v)` in the `undir` vector.
    pub fn new(g: LGraph, u: Rc<LNode>, v: Rc<LNode>) -> Self {
        Self {
            g,
            undir: vec![(u, v)],
            canonic: Vec::new(),
            building: Vec::new(),
            queue: Vec::new(),
        }
    }

    /// Returns the neighbours in the `undir` vector for a given node `u`.
    fn get_neighbours(&self, u: Rc<LNode>) -> Vec<Rc<LNode>> {
        self.undir
            .iter()
            .filter(|(x, y)| x == &u || y == &u)
            .map(|(x, y)| if *x == u { y.clone() } else { x.clone() })
            .collect()
    }

    /// Function that populates the entries of the current state. It uses two internal functions, namely
    /// - `build_equivalence_class`: build the equivalence class for a given node.
    /// - `enqueue_and_propagate`: creates a queue of the homogeneous node in an equivalence class.
    /// On callback termination, it is expected that the field `undir` contains pairs `(u, v)` such that `u ~ v` where
    /// `~` is the equivalence relation described in the [paper of reference](https://arxiv.org/pdf/1907.06101.pdf)
    pub fn blind_check(&mut self) -> Result<(), String> {
        for node in self.g.nodes.clone() {
            if self.canonic.iter().position(|(x, _)| x == &node).is_none() {
                if let Err(e) = self.build_equivalence_class(node) {
                    return Err(e);
                }
            }
        }

        Ok(())
    }

    fn build_equivalence_class(&mut self, c: Rc<LNode>) -> Result<(), String> {
        self.canonic.push((c.clone(), c.clone()));
        self.queue
            .push((c.clone(), VecDeque::from(vec![c.clone()])));

        loop {
            let n;
            if let Some(k) = self.queue.iter().position(|(x, _)| x == &c) {
                n = self.queue[k].1.pop_front();
            } else {
                break;
            }

            if n.is_none() {
                break;
            }

            let n = n.unwrap();

            // For every parent m of n build the equivalence class. This is done in order to achieve stability in the
            // algorithm. One can strat from a node that is not a root, and the algorithm would still be valid.
            // If the pattern doesn't match, we are analyzing a root.
            for m in n.get_parent() {
                if let Some(m) = m.upgrade() {
                    if let Some(k) = self.canonic.iter().position(|(x, _)| x == &m) {
                        let c1 = self.canonic[k].1.clone();
                        if self
                            .building
                            .iter()
                            .find(|(x, _)| x == &c1)
                            .unwrap_or(&(c1, false))
                            .1
                        {
                            return Err("Parent still building".to_string());
                        }
                    } else {
                        if let Err(e) = self.build_equivalence_class(m.clone()) {
                            return Err(e);
                        }
                    }
                }
            }

            // For every neighbour m of n propagate the query over the lambda graph.
            for m in self.get_neighbours(n.clone()) {
                match self.canonic.iter().find(|(x, _)| x == &m) {
                    None => {
                        if let Err(e) = self.enqueue_and_propagate(m.clone(), c.clone()) {
                            return Err(e);
                        }
                    }
                    Some((_, k)) => {
                        if &c != k {
                            return Err(
                                format!("Error, found two different representatives for node {:?} ({:?}): ({:?}, {:?})", m, n, c, k)
                            );
                        }
                    }
                }
            }
        }

        if let Some(k) = self.building.iter().position(|(x, _)| x == &c) {
            self.building[k] = (c.clone(), false);
        }

        Ok(())
    }

    fn enqueue_and_propagate(&mut self, m: Rc<LNode>, c: Rc<LNode>) -> Result<(), String> {
        match (m.as_ref(), c.as_ref()) {
            (App(l1, r1, _), App(l2, r2, _)) => {
                self.undir.push((l1.clone(), l2.clone()));
                self.undir.push((r1.clone(), r2.clone()));
            }
            (Abs(l1, _), Abs(l2, _)) => {
                self.undir.push((l1.clone(), l2.clone()));
            }
            (BVar(_, _), BVar(_, _)) | (Var(_), Var(_)) => (),
            (_, _) => return Err("Compared two different kind of nodes.".to_string()),
        }

        if let Some(k) = self.canonic.iter().position(|(x, _)| x == &m) {
            self.canonic[k] = (m.clone(), c.clone())
        } else {
            self.canonic.push((m.clone(), c.clone()))
        }
        
        if let Some(k) = self.queue.iter().position(|(x, _)| x == &c) {
            self.queue[k].1.push_back(m.clone());
        } else {
            self.queue
                .push((c.clone(), VecDeque::from(vec![m.clone()])));
        }

        Ok(())
    }

    pub fn var_check(&self) -> Result<(), String> {
        let g = self.g.clone();
        let nodes = g.nodes.iter().filter(|x| match x.as_ref() {
            Var(_) => true,
            BVar(_, _) => true,
            _ => false,
        });

        for v in nodes {
            let w = self.canonic.iter().find(|(x, _)| x == v).unwrap().1.clone();
            let v = v.as_ref();
            let w = w.as_ref();

            if v != w {
                match (v, w) {
                    (Var(_), _) | (_, Var(_)) => {
                        let err = format!(
                            "Error: found homogeneous node for unbound variable.\n{:?} {:?}",
                            v, w
                        );
                        return Err(err);
                    }
                    (BVar(x, _), BVar(y, _)) => {
                        let x = x.borrow().upgrade().unwrap();
                        let y = y.borrow().upgrade().unwrap();
                        let bx = self
                            .canonic
                            .iter()
                            .find(|(l, _)| *l == x)
                            .unwrap()
                            .clone()
                            .1;
                        let by = self
                            .canonic
                            .iter()
                            .find(|(l, _)| *l == y)
                            .unwrap()
                            .clone()
                            .1;

                        if bx != by {
                            return Err("Error: parents have different canonic forms. canonic(p(v)) != canonic(p(w))".to_string());
                        }
                    }
                    _ => (),
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    #[test]
    fn test() {
        let var1 = Rc::new(BVar(RefCell::new(Weak::new()), RefCell::new(Vec::new())));
        let abs1 = Rc::new(Abs(var1.clone(), RefCell::new(Vec::new())));
        let app1 = Rc::new(App(abs1.clone(), abs1.clone(), RefCell::new(Vec::new())));

        let var2 = Rc::new(BVar(RefCell::new(Weak::new()), RefCell::new(Vec::new())));
        let abs2 = Rc::new(Abs(var2.clone(), RefCell::new(Vec::new())));
        let app2 = Rc::new(App(abs2.clone(), abs2.clone(), RefCell::new(Vec::new())));
        let root1 = Rc::new(App(app1.clone(), app2.clone(), RefCell::new(Vec::new())));

        let var3 = Rc::new(BVar(RefCell::new(Weak::new()), RefCell::new(Vec::new())));
        let abs3 = Rc::new(Abs(var3.clone(), RefCell::new(Vec::new())));
        let app3 = Rc::new(App(abs3.clone(), abs3.clone(), RefCell::new(Vec::new())));
        let root2 = Rc::new(App(app3.clone(), app3.clone(), RefCell::new(Vec::new())));

        // Setting up the parents.
        var1.add_parent(abs1.clone());
        abs1.add_parent(app1.clone());
        app1.add_parent(root1.clone());
        var2.add_parent(abs2.clone());
        abs2.add_parent(app2.clone());
        app2.add_parent(root1.clone());
        var3.add_parent(abs3.clone());
        abs3.add_parent(app3.clone());
        app3.add_parent(root2.clone());

        // Bound the variable nodes.
        var3.add_abs(abs3.clone());
        var2.add_abs(abs2.clone());
        var1.add_abs(abs1.clone());

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
        // g.nodes.iter().for_each(|n| println!("{:?}", n));
        
        let mut s = State::new(g, root1.clone(), root2.clone());
        let result = s.blind_check();
        assert!(result.is_ok());

        match result {
            Ok(_) => {
                println!("Blind check ok");

                println!("CANONIC EDGES");
                s.canonic.iter().for_each(|x| println!("{:?}", x));
            }
            Err(e) => {
                println!("{}", e);
                println!("CANONIC EDGES");
                s.canonic.iter().for_each(|x| println!("{:?}", x));
            }
        }

        if let Err(e) = s.var_check() {
            println!("{}", e);
        }
    }
}
