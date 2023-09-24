use std::{
    cell::RefCell,
    collections::VecDeque,
    fmt::Debug,
    ptr,
    rc::{Rc, Weak},
};

use LNode::*;

/// Enum representing a lambda node. Such node can have three forms:
/// - Application: an application node has two children.
/// - Abstraction: an abstraction node has one child.
/// - Variable: this kind of node can represent bound and unbound variables.
#[derive(Clone)]
#[allow(dead_code)]
pub enum LNode {
    App {
        left: Rc<Self>,
        right: Rc<Self>,
        parent: RefCell<Vec<Weak<Self>>>,
        undir: RefCell<Vec<Weak<Self>>>,
        canonic: RefCell<Weak<Self>>,
        building: RefCell<bool>,
        queue: RefCell<VecDeque<Weak<Self>>>,
        // t: Option<Rc<Self>>,
    },
    Abs {
        body: Rc<Self>,
        parent: RefCell<Vec<Weak<Self>>>,
        undir: RefCell<Vec<Weak<Self>>>,
        canonic: RefCell<Weak<Self>>,
        building: RefCell<bool>,
        queue: RefCell<VecDeque<Weak<Self>>>,
        // t: Option<Rc<Self>>,
    },
    BVar {
        binder: RefCell<Weak<Self>>,
        parent: RefCell<Vec<Weak<Self>>>,
        undir: RefCell<Vec<Weak<Self>>>,
        canonic: RefCell<Weak<Self>>,
        building: RefCell<bool>,
        queue: RefCell<VecDeque<Weak<Self>>>,
        t: Option<Rc<Self>>,
    },
    Var {
        parent: RefCell<Vec<Weak<Self>>>,
        undir: RefCell<Vec<Weak<Self>>>,
        canonic: RefCell<Weak<Self>>,
        building: RefCell<bool>,
        queue: RefCell<VecDeque<Weak<Self>>>,
        t: Option<Rc<Self>>,
    },
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
            Abs { body, .. } => f
                .debug_struct("Abs")
                .field("body", body)
                // .field("t", t)
                .finish(),
            App { left, right, .. } => f
                .debug_struct("App")
                .field("left", left)
                .field("right", right)
                // .field("t", t)
                .finish(),
            BVar { binder, t, .. } => f
                .debug_struct("BVar")
                .field("binder", binder)
                .field("t", t)
                .finish(),
            Var { t, .. } => f.debug_struct("Var").field("t", t).finish(),
        }
    }
}

#[allow(dead_code)]
impl LNode {
    /// Adds to the current node a new parent pointer `p`.
    pub(crate) fn add_parent(&self, p: Rc<LNode>) {
        let parent = Rc::downgrade(&p);
        match self {
            App { parent: p, .. } => p.borrow_mut().push(parent),
            Abs { parent: p, .. } => p.borrow_mut().push(parent),
            BVar { parent: p, .. } => p.borrow_mut().push(parent),
            Var { parent: p, .. } => p.borrow_mut().push(parent),
        }
    }

    pub fn new_app(left: Rc<Self>, right: Rc<Self>) -> Self {
        App {
            left,
            right,
            // t,
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        }
    }

    pub fn new_abs(body: Rc<Self>) -> Self {
        Abs {
            body,
            // t,
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        }
    }

    pub fn new_var(t: Option<Rc<Self>>) -> Self {
        Var {
            t,
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        }
    }

    pub fn new_bvar(t: Option<Rc<Self>>) -> Self {
        BVar {
            binder: RefCell::new(Weak::new()),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
            t,
        }
    }

    pub(crate) fn is_abs(&self) -> bool {
        matches!(self, Abs { .. })
    }

    pub(crate) fn is_bvar(&self) -> bool {
        matches!(self, BVar { .. })
    }

    pub(crate) fn is_var(&self) -> bool {
        matches!(self, Var { .. })
    }

    pub(crate) fn is_app(&self) -> bool {
        matches!(self, App { .. })
    }

    pub fn get_type(&self) -> Option<Rc<Self>> {
        match self {
            App { .. } => None,
            Abs { .. } => None,
            Var { t, .. } => t.clone(),
            BVar { t, .. } => t.clone(),
        }
    }

    pub(crate) fn undir(&self) -> &RefCell<Vec<Weak<Self>>> {
        match self {
            App { undir, .. } => undir,
            Abs { undir, .. } => undir,
            BVar { undir, .. } => undir,
            Var { undir, .. } => undir,
        }
    }

    pub(crate) fn canonic(&self) -> &RefCell<Weak<Self>> {
        match self {
            App { canonic, .. } => canonic,
            Abs { canonic, .. } => canonic,
            BVar { canonic, .. } => canonic,
            Var { canonic, .. } => canonic,
        }
    }

    pub(crate) fn building(&self) -> &RefCell<bool> {
        match self {
            App { building, .. } => building,
            Abs { building, .. } => building,
            BVar { building, .. } => building,
            Var { building, .. } => building,
        }
    }

    pub(crate) fn queue(&self) -> &RefCell<VecDeque<Weak<Self>>> {
        match self {
            App { queue, .. } => queue,
            Abs { queue, .. } => queue,
            BVar { queue, .. } => queue,
            Var { queue, .. } => queue,
        }
    }

    /// Returns the reference to the parent of the current node.
    pub(crate) fn get_parent(&self) -> Vec<Weak<Self>> {
        let parent = match self {
            App { parent, .. } => parent,
            Abs { parent, .. } => parent,
            BVar { parent, .. } => parent,
            Var { parent, .. } => parent,
        };

        parent.borrow().clone()
    }

    /// Binds a `BVar` node to an `Abs` node.
    pub(crate) fn bind_to(&self, abs: Rc<LNode>) {
        if !self.is_bvar() || abs.is_abs() {
            // TODO: fail
        }

        let abs = Rc::downgrade(&abs);
        match &*self {
            BVar { binder, .. } => *binder.borrow_mut() = abs,
            _ => (),
        }
    }
}
