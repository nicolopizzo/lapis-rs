use std::{
    cell::RefCell,
    collections::VecDeque,
    fmt::Debug,
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
    },
    Abs {
        body: Rc<Self>,
        parent: RefCell<Vec<Weak<Self>>>,
        undir: RefCell<Vec<Weak<Self>>>,
        canonic: RefCell<Weak<Self>>,
        building: RefCell<bool>,
        queue: RefCell<VecDeque<Weak<Self>>>,
    },
    BVar {
        binder: RefCell<Weak<Self>>,
        parent: RefCell<Vec<Weak<Self>>>,
        undir: RefCell<Vec<Weak<Self>>>,
        canonic: RefCell<Weak<Self>>,
        building: RefCell<bool>,
        queue: RefCell<VecDeque<Weak<Self>>>,
    },
    Var {
        parent: RefCell<Vec<Weak<Self>>>,
        undir: RefCell<Vec<Weak<Self>>>,
        canonic: RefCell<Weak<Self>>,
        building: RefCell<bool>,
        queue: RefCell<VecDeque<Weak<Self>>>,
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
            Abs {
                body: _,
                parent: _,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => f.write_fmt(format_args!("Abs: {:p}", self)),
            App {
                left: _,
                right: _,
                parent: _,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => f.write_fmt(format_args!("App: {:p}", self)),
            BVar {
                binder: _,
                parent: _,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => f.write_fmt(format_args!("Var: {:p}", self)),
            Var {
                parent: _,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => f.write_fmt(format_args!("Var: {:p}", self)),
        }
    }
}

#[allow(dead_code)]
impl LNode {
    /// Adds to the current node a new parent pointer `p`.
    pub(crate) fn add_parent(&self, p: Rc<LNode>) {
        let parent = Rc::downgrade(&p);
        match self {
            App {
                left: _,
                right: _,
                parent: p,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => p.borrow_mut().push(parent),
            Abs {
                body: _,
                parent: p,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => p.borrow_mut().push(parent),
            BVar {
                binder: _,
                parent: p,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => p.borrow_mut().push(parent),
            Var {
                parent: p,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => p.borrow_mut().push(parent),
        }
    }

    pub fn new_app(left: Rc<LNode>, right: Rc<LNode>) -> Self {
        App {
            left,
            right,
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        }
    }

    pub fn new_abs(body: Rc<LNode>) -> Self {
        Abs {
            body,
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        }
    }

    pub fn new_var() -> Self {
        Var {
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        }
    }

    pub(crate) fn is_abs(&self) -> bool {
        matches!(
            self,
            Abs {
                body: _,
                parent: _,
                undir: _,
                canonic: _,
                building: _,
                queue: _
            }
        )
    }

    pub(crate) fn is_bvar(&self) -> bool {
        matches!(
            self,
            BVar {
                binder: _,
                parent: _,
                undir: _,
                canonic: _,
                building: _,
                queue: _
            }
        )
    }

    pub(crate) fn is_var(&self) -> bool {
        matches!(
            self,
            Var {
                parent: _,
                undir: _,
                canonic: _,
                building: _,
                queue: _
            }
        )
    }

    pub(crate) fn is_app(&self) -> bool {
        matches!(
            self,
            App {
                left: _,
                right: _,
                parent: _,
                undir: _,
                canonic: _,
                building: _,
                queue: _
            }
        )
    }

    pub(crate) fn undir(&self) -> &RefCell<Vec<Weak<Self>>> {
        match self {
            App {
                left: _,
                right: _,
                parent: _,
                undir,
                canonic: _,
                building: _,
                queue: _,
            } => undir,
            Abs {
                body: _,
                parent: _,
                undir,
                canonic: _,
                building: _,
                queue: _,
            } => undir,
            BVar {
                binder: _,
                parent: _,
                undir,
                canonic: _,
                building: _,
                queue: _,
            } => undir,
            Var {
                parent: _,
                undir,
                canonic: _,
                building: _,
                queue: _,
            } => undir,
        }
    }

    pub(crate) fn canonic(&self) -> &RefCell<Weak<Self>> {
        match self {
            App {
                left: _,
                right: _,
                parent: _,
                undir: _,
                canonic,
                building: _,
                queue: _,
            } => canonic,
            Abs {
                body: _,
                parent: _,
                undir: _,
                canonic,
                building: _,
                queue: _,
            } => canonic,
            BVar {
                binder: _,
                parent: _,
                undir: _,
                canonic,
                building: _,
                queue: _,
            } => canonic,
            Var {
                parent: _,
                undir: _,
                canonic,
                building: _,
                queue: _,
            } => canonic,
        }
    }

    pub(crate) fn building(&self) -> &RefCell<bool> {
        match self {
            App {
                left: _,
                right: _,
                parent: _,
                undir: _,
                canonic: _,
                building,
                queue: _,
            } => building,
            Abs {
                body: _,
                parent: _,
                undir: _,
                canonic: _,
                building,
                queue: _,
            } => building,
            BVar {
                binder: _,
                parent: _,
                undir: _,
                canonic: _,
                building,
                queue: _,
            } => building,
            Var {
                parent: _,
                undir: _,
                canonic: _,
                building,
                queue: _,
            } => building,
        }
    }

    pub(crate) fn queue(&self) -> &RefCell<VecDeque<Weak<Self>>> {
        match self {
            App {
                left: _,
                right: _,
                parent: _,
                undir: _,
                canonic: _,
                building: _,
                queue,
            } => queue,
            Abs {
                body: _,
                parent: _,
                undir: _,
                canonic: _,
                building: _,
                queue,
            } => queue,
            BVar {
                binder: _,
                parent: _,
                undir: _,
                canonic: _,
                building: _,
                queue,
            } => queue,
            Var {
                parent: _,
                undir: _,
                canonic: _,
                building: _,
                queue,
            } => queue,
        }
    }

    /// Returns the reference to the parent of the current node.
    pub(crate) fn get_parent(&self) -> Vec<Weak<Self>> {
        let p = match self {
            App {
                left: _,
                right: _,
                parent: p,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => p,
            Abs {
                body: _,
                parent: p,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => p,
            BVar {
                binder: _,
                parent: p,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => p,
            Var {
                parent: p,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => p,
        };

        let p = p.borrow();
        let p = p.clone();
        p
    }

    /// Binds a `BVar` node to an `Abs` node.
    pub(crate) fn bind_to(&self, abs: Rc<LNode>) {
        if !self.is_bvar() || abs.is_abs() {
            // TODO: fail
        }
        let abs = Rc::downgrade(&abs);
        match &*self {
            BVar {
                binder: x,
                parent: _,
                canonic: _,
                undir: _,
                building: _,
                queue: _,
            } => *x.borrow_mut() = abs,
            _ => (),
        }
    }
}
