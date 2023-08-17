use std::{
    collections::{HashMap, VecDeque},
    hash::Hash, fmt::Display,
};

#[derive(Debug, Clone)]
pub struct LGraph<'a> {
    pub nodes: Vec<LNode<'a>>,
}

impl<'a> LGraph<'a> {
    pub fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    pub fn add_node(&mut self, node: LNode<'a>) {
        self.nodes.push(node);
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum LNode<'a> {
    App(&'a Self, &'a Self),
    Abs(&'a Self),
    Var,
    BVar,
}

pub use LNode::*;

#[derive(Clone, Debug)]
pub struct State<'a> {
    g: LGraph<'a>,
    undir: Vec<(LNode<'a>, LNode<'a>)>,     //undirected edges
    canonic: HashMap<LNode<'a>, LNode<'a>>, // canonic edges
    building: HashMap<LNode<'a>, bool>,
    queue: HashMap<LNode<'a>, VecDeque<LNode<'a>>>,
}

impl<'a> State<'a> {
    pub fn new(g: LGraph<'a>) -> Self {
        Self {
            g,
            undir: Vec::new(),
            canonic: HashMap::new(),
            building: HashMap::new(),
            queue: HashMap::new(),
        }
    }

    pub fn get_neighbours(&self, c: &LNode<'a>) -> Vec<LNode<'a>> {
        let mut res = Vec::new();
        for (u, v) in self.undir.clone() {
            if &u == c {
                res.push(v);
            }
        }
        res
    }
}

pub fn blind_check<'a>(g: &'a LGraph<'a>) -> Result<State<'a>, String> {
    let mut s = State::new(g.to_owned());
    for n in s.g.nodes.clone() {
        if s.canonic.get(&n).is_none() {
            if let Err(e) = build_equivalence_class(&n, &mut s) {
                return Err(e);
            }
        }
    }

    Ok(s)
}

pub fn build_equivalence_class<'a>(c: &LNode<'a>, s: &mut State<'a>) -> Result<(), String> {
    s.canonic.insert(c.clone(), c.clone());
    s.building.insert(c.clone(), true);
    s.queue.insert(c.clone(), VecDeque::from(vec![c.clone()]));

    loop {
        let n = s.queue.get_mut(c).unwrap().pop_front();
        if n.is_none() {
            break;
        }

        let n = n.unwrap();
        // For every parent m of n...
        // TODO: add parent pointer

        // For every neighbour m of n...
        for m in s.get_neighbours(&n) {
            match s.canonic.get(&m) {
                None => {
                    if let Err(e) = enqueue_and_propagate(&m, c, s) {
                        return Err(e);
                    }
                }
                Some(k) => {
                    if c != k {
                        // TODO: Fail
                        return Err("Error".to_string());
                    }
                }
            }
        }
    }

    s.building.insert(c.clone(), false);
    Ok(())
}

pub fn enqueue_and_propagate<'a>(
    m: &LNode<'a>,
    c: &LNode<'a>,
    s: &mut State<'a>,
) -> Result<(), String> {
    match (m, c) {
        (Abs(&p), Abs(&q)) => {
            // add edge p ~ q
            s.undir.push((p.clone(), q.clone()))
        }
        (App(&p1, &p2), App(&q1, &q2)) => {
            // add edge p1 ~ q1
            s.undir.push((p1.clone(), q1.clone()));

            // add edge p2 ~ q2
            s.undir.push((p2.clone(), q2.clone()));
        }
        (BVar, BVar) => (),
        (Var, Var) => (),
        (_, _) => {
            return Err("Error: compared two different kind of nodes.".to_string());
        }
    }

    s.canonic.insert(m.clone(), c.clone());
    s.queue.get_mut(c).unwrap().push_back(m.clone());
    Ok(())
}
