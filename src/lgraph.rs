use std::{
    cell::RefCell,
    collections::VecDeque,
    fmt::{Debug, Pointer, format},
    rc::{Rc, Weak},
};

/// Alias for `Rc<RefCell<T>>`
pub type RcRef<T> = Rc<RefCell<T>>;
/// Alias for `Weak<RefCell<T>>`
pub type WkRef<T> = Weak<RefCell<T>>;

use LNode::*;

/// Enum representing a lambda node. Such node can have three forms:
/// - Application: an application node has two children
/// - Abstraction: an abstraction node has one child
/// - Variable: this kind of node can represent bound and unbound variables. To distinguish between the two of them, we use an `Option` field
/// Each variant of the enum also has a Weak reference field: this field points to the parent node.
#[derive(Clone)]
pub enum LNode {
    App(RcRef<Self>, RcRef<Self>, WkRef<Self>),
    Abs(RcRef<Self>, WkRef<Self>),
    Var(Option<WkRef<Self>>, WkRef<Self>),
}

/// Implementing runtime equality for LNode.
impl PartialEq for LNode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Abs(l1, p1), Abs(l2, p2)) => address_of(l1) == address_of(l2),
            (App(l1, r1, p1), App(l2, r2, p2)) => {
                address_of(l1) == address_of(l2) && address_of(r1) == address_of(r2)
            }
            (Var(_, _), Var(_, _)) => address_of(self) == address_of(other),
            (_, _) => false,
        }
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
            Var(_, _) => f.write_fmt(format_args!("Var: {:p}", self)),
        }
    }
}

impl LNode {
    /// Modifies the current node parent pointer with `p`. It has not a public
    fn add_parent(&mut self, p: RcRef<LNode>) {
        let parent = Rc::downgrade(&p);
        *self = match self.clone() {
            App(l, r, _) => App(l, r, parent),
            Abs(l, _) => Abs(l, parent),
            Var(l, _) => Var(l, parent),
        }
    }

    /// Returns the pointer to the current node, used for clearer syntax: instead of writing
    /// `Rc::new(RefCell::new(node))` one can write `node.as_ref()` to obtain the same result in a clearer way.
    pub fn as_ref(self) -> RcRef<Self> {
        Rc::new(RefCell::new(self))
    }

    /// Returns the reference to the parent of the current node.
    pub fn get_parent(&self) -> WkRef<Self> {
        let p = match self {
            App(_, _, p) => p,
            Abs(_, p) => p,
            Var(_, p) => p,
        };

        p.clone()
    }

    pub fn add_abs(&mut self, v: RcRef<LNode>) {
        let abs = Rc::downgrade(&v);
        *self = match self.clone() {
            Var(_, p) => Var(Some(abs), p),
            x => x,
        }
    }
}

/// This trait permits to use a simple and intuitive syntax for working with variables with type `Rc<RefCell<LNode>>`, in particular when adding or retreiving the parent node.
/// # Example
/// ```
/// // the method `as_ref()` returns a `RcRef<LNode>`
/// let var1 = Var(None, Weak::new()).as_ref();
/// let abs1 = Abs(var1.clone(), Weak::new()).as_ref();
/// var1.add_parent(abs1.clone());
/// ```
pub trait RefNode {
    fn add_parent(&self, v: Rc<RefCell<LNode>>);
    fn add_abs(&self, v: Rc<RefCell<LNode>>);
    fn get_parent(&self) -> WkRef<LNode>;
}

impl RefNode for RcRef<LNode> {
    fn add_parent(&self, v: Rc<RefCell<LNode>>) {
        self.as_ref().borrow_mut().add_parent(v.clone());
    }

    fn add_abs(&self, v: RcRef<LNode>) {
        self.as_ref().borrow_mut().add_abs(v.clone());
    }

    fn get_parent(&self) -> WkRef<LNode> {
        self.as_ref().borrow().get_parent()
    }
}

/// Structure that defines a Lambda-Graph (see [this](https://arxiv.org/pdf/1907.06101.pdf)).
#[derive(Clone, Debug)]
pub struct LGraph {
    nodes: Vec<RcRef<LNode>>,
}

impl LGraph {
    /// Returns an empty LGraph.
    pub fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    /// Returns an LGraph that has `v` as nodes.
    pub fn from(v: Vec<RcRef<LNode>>) -> Self {
        Self { nodes: v }
    }

    /// Adds `node` to the nodes of the graph.
    pub fn add_node(&mut self, node: RcRef<LNode>) {
        self.nodes.push(node);
    }
}

/// Structure holding the information to build the equivalence classes over a lambda graph.
#[derive(Clone, Debug)]
pub struct State {
    g: LGraph,
    undir: Vec<(RcRef<LNode>, RcRef<LNode>)>, //undirected edges
    canonic: Vec<(RcRef<LNode>, RcRef<LNode>)>, // canonic edges
    building: Vec<(RcRef<LNode>, bool)>,
    queue: Vec<(RcRef<LNode>, VecDeque<RcRef<LNode>>)>,
}

impl State {
    /// Returns a new state with an initial edge `(u, v)` in the `undir` vector.
    pub fn new(g: LGraph, u: RcRef<LNode>, v: RcRef<LNode>) -> Self {
        Self {
            g,
            undir: vec![(u, v)],
            canonic: Vec::new(),
            building: Vec::new(),
            queue: Vec::new(),
        }
    }

    /// Returns the neighbours in the `undir` vector for a given node `u`.
    fn get_neighbours(&self, u: RcRef<LNode>) -> Vec<RcRef<LNode>> {
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

    fn build_equivalence_class(&mut self, c: RcRef<LNode>) -> Result<(), String> {
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
            if let Some(m) = n.get_parent().upgrade() {
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

            // For every neighbour m of n propagate the query over the lambda graph.
            for m in self.get_neighbours(n.clone()) {
                // println!("m: {:?}", m);
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

    fn enqueue_and_propagate(&mut self, m: RcRef<LNode>, c: RcRef<LNode>) -> Result<(), String> {
        let m1 = &*m.borrow();
        let c1 = &*c.borrow();
        match (m1, c1) {
            (App(l1, r1, _), App(l2, r2, _)) => {
                self.undir.push((l1.clone(), l2.clone()));
                self.undir.push((r1.clone(), r2.clone()));
            }
            (Abs(l1, _), Abs(l2, _)) => {
                self.undir.push((l1.clone(), l2.clone()));
            }
            (Var(_, _), Var(_, _)) => (),
            (_, _) => return Err("Compared two different kind of nodes.".to_string()),
        }

        // canonic(m) := c
        if let Some(k) = self.canonic.iter().position(|(x, _)| x == &m) {
            self.canonic[k] = (m.clone(), c.clone())
        } else {
            self.canonic.push((m.clone(), c.clone()))
        }
        // queue(c).push(m)
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
        let nodes = g.nodes.iter().filter(|x| match &*x.borrow() {
            Var(_, _) => true,
            _ => false,
        });

        for v in nodes {
            let w = self.canonic.iter().find(|(x, _)| x == v).unwrap().1.clone();
            let v = &*v.borrow();
            let w = &*w.borrow();

            if v != w {
                match (v, w) {
                    (Var(None, _), _) | (_, Var(None, _)) => {
                        let err = format!("Error: found homogeneous node for unbound variable.\n{:?} {:?}", v, w);
                        return Err(err);
                    }
                    (Var(Some(x), _), Var(Some(y), _)) => {
                        let x = x.upgrade().unwrap();
                        let y = y.upgrade().unwrap();
                        let bx = self
                            .canonic
                            .iter()
                            .find(|(l, _)| l == &x)
                            .unwrap()
                            .clone()
                            .1;
                        let by = self
                            .canonic
                            .iter()
                            .find(|(l, _)| l == &y)
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

fn address_of<T>(x: &T) -> u64 {
    let str_addr = format!("{:p}", x);
    u64::from_str_radix(str_addr.trim_start_matches("0x"), 16).unwrap()
}

#[cfg(test)]
mod tests {

    use super::*;
    #[test]
    fn test() {
        let var1 = Var(None, Weak::new()).as_ref();
        let abs1 = Abs(var1.clone(), Weak::new()).as_ref();
        let app1 = App(abs1.clone(), abs1.clone(), Weak::new()).as_ref();

        let var2 = Var(None, Weak::new()).as_ref();
        let abs2 = Abs(var2.clone(), Weak::new()).as_ref();
        let app2 = App(abs2.clone(), abs2.clone(), Weak::new()).as_ref();
        let root1 = App(app1.clone(), app2.clone(), Weak::new()).as_ref();

        let var3 = Var(None, Weak::new()).as_ref();
        let abs3 = Abs(var3.clone(), Weak::new()).as_ref();
        let app3 = App(abs3.clone(), abs3.clone(), Weak::new()).as_ref();
        let root2 = App(app3.clone(), app3.clone(), Weak::new()).as_ref();

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
        // var3.add_abs(abs3.clone());
        // var2.add_abs(abs2.clone());
        // var1.add_abs(abs1.clone());

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

        // FIXME: unbound variables get put in an homogeneous classs
        if let Err(e) = s.var_check() {
            println!("{}", e);
        }
        // let result = s.var_check();
        // assert!(result.is_ok());
    }
}
