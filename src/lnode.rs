use std::{
    cell::RefCell,
    collections::VecDeque,
    fmt::{Debug, Write},
    hash::Hash,
    rc::{Rc, Weak},
};

use LNode::*;

/// Enum representing a lambda node. Such node can have three forms:
/// - Application: an application node has two children.
/// - Abstraction: an abstraction node has one child.
/// - Variable: this kind of node can represent bound and unbound variables.
#[derive(Clone)]
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
    Prod {
        bvar: Rc<Self>,
        body: Rc<Self>,
        parent: RefCell<Vec<Weak<Self>>>,
        undir: RefCell<Vec<Weak<Self>>>,
        canonic: RefCell<Weak<Self>>,
        building: RefCell<bool>,
        queue: RefCell<VecDeque<Weak<Self>>>,
    },
    Abs {
        bvar: Rc<Self>,
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
        subs_to: RefCell<Option<Rc<Self>>>,
        // ty must be a `Prod` or a `Var` node.
        ty: Option<Rc<Self>>,
    },
    Var {
        parent: RefCell<Vec<Weak<Self>>>,
        undir: RefCell<Vec<Weak<Self>>>,
        canonic: RefCell<Weak<Self>>,
        building: RefCell<bool>,
        queue: RefCell<VecDeque<Weak<Self>>>,
        // ty must be a `Prod` or a `Var` node.
        ty: Option<Rc<Self>>,
    },
    Type,
    Kind,
}

/// Implementing runtime equality for LNode.
impl PartialEq for LNode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type, Type) => true,
            (Kind, Kind) => true,
            (_, _) => std::ptr::eq(self, other),
        }
    }

    fn ne(&self, other: &Self) -> bool {
        !Self::eq(self, other)
    }
}

impl Debug for LNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Abs { body, .. } => f.debug_struct("Abs").field("body", body).finish(),
            App { left, right, .. } => f
                .debug_struct("App")
                .field("left", left)
                .field("right", right)
                .finish(),
            Prod { bvar, body, .. } => f
                .debug_struct("Prod")
                .field("bvar", bvar)
                .field("body", body)
                .finish(),
            BVar { ty, .. } => {
                let subs = self.get_sub();
                if subs.is_some() {
                    let subs = subs.unwrap();
                    f.debug_struct("Sub").finish()?;
                    subs.fmt(f)
                } else {
                    f.debug_struct("BVar").field("t", ty).finish()
                }
            }
            Var { ty, .. } => f.debug_struct("Var").field("ty", ty).finish(),
            Type => f.write_str("Type"),
            Kind => f.write_str("Kind"),
        }
    }
}

impl Hash for LNode {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::ptr::addr_of!(self).hash(state);
    }
}

impl Eq for LNode {}

#[allow(dead_code)]
impl LNode {
    /// Adds to the current node a new parent pointer `p`.
    pub(crate) fn add_parent(&self, p: Rc<LNode>) {
        let parent = Rc::downgrade(&p);
        match self {
            App { parent: p, .. } => p.borrow_mut().push(parent),
            Prod { parent: p, .. } => p.borrow_mut().push(parent),
            Abs { parent: p, .. } => p.borrow_mut().push(parent),
            BVar { parent: p, .. } => p.borrow_mut().push(parent),
            Var { parent: p, .. } => p.borrow_mut().push(parent),
            Type => unreachable!(),
            Kind => unreachable!(),
        }
    }

    pub fn new_app(left: Rc<Self>, right: Rc<Self>) -> Self {
        let app = App {
            left: left.clone(),
            right: right.clone(),
            // t,
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        };

        app
    }

    pub fn new_prod(bvar: Rc<Self>, body: Rc<Self>) -> Self {
        Prod {
            bvar,
            body,
            // t,
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        }
    }

    pub fn new_abs(bvar: Rc<Self>, body: Rc<Self>) -> Self {
        Abs {
            bvar,
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
            ty: t,
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
            subs_to: RefCell::new(None),
            ty: t,
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
            Var { ty: t, .. } => t.clone(),
            BVar { ty: t, .. } => t.clone(),
            _ => None,
        }
    }

    /// Reset all fields for sharing equality algorithm.
    pub fn reset(&self) {
        self.set_canonic(Weak::new());
        self.set_building(false);
        *self.undir().borrow_mut() = Vec::new();
        *self.queue().borrow_mut() = VecDeque::new();
    }

    pub(crate) fn undir(&self) -> &RefCell<Vec<Weak<Self>>> {
        match self {
            App { undir, .. } => undir,
            Prod { undir, .. } => undir,
            Abs { undir, .. } => undir,
            BVar { undir, .. } => undir,
            Var { undir, .. } => undir,
            Type => unreachable!(),
            Kind => unreachable!(),
        }
    }

    pub(crate) fn canonic(&self) -> &RefCell<Weak<Self>> {
        match self {
            App { canonic, .. } => canonic,
            Prod { canonic, .. } => canonic,
            Abs { canonic, .. } => canonic,
            BVar { canonic, .. } => canonic,
            Var { canonic, .. } => canonic,
            Type => unreachable!(),
            Kind => unreachable!(),
        }
    }

    pub(crate) fn set_canonic(&self, value: Weak<Self>) {
        match self {
            App { canonic, .. } => *canonic.borrow_mut() = value,
            Prod { canonic, .. } => *canonic.borrow_mut() = value,
            Abs { canonic, .. } => *canonic.borrow_mut() = value,
            BVar { canonic, .. } => *canonic.borrow_mut() = value,
            Var { canonic, .. } => *canonic.borrow_mut() = value,
            Type => unreachable!(),
            Kind => unreachable!(),
        }
    }

    pub(crate) fn building(&self) -> &RefCell<bool> {
        match self {
            App { building, .. } => building,
            Prod { building, .. } => building,
            Abs { building, .. } => building,
            BVar { building, .. } => building,
            Var { building, .. } => building,
            Type => unreachable!(),
            Kind => unreachable!(),
        }
    }

    pub(crate) fn set_building(&self, b: bool) {
        match self {
            App { building, .. } => *building.borrow_mut() = b,
            Prod { building, .. } => *building.borrow_mut() = b,
            Abs { building, .. } => *building.borrow_mut() = b,
            BVar { building, .. } => *building.borrow_mut() = b,
            Var { building, .. } => *building.borrow_mut() = b,
            Type => unreachable!(),
            Kind => unreachable!(),
        }
    }

    pub(crate) fn queue(&self) -> &RefCell<VecDeque<Weak<Self>>> {
        match self {
            App { queue, .. } => queue,
            Prod { queue, .. } => queue,
            Abs { queue, .. } => queue,
            BVar { queue, .. } => queue,
            Var { queue, .. } => queue,
            Type => unreachable!(),
            Kind => unreachable!(),
        }
    }

    /// Returns the reference to the parent of the current node.
    pub(crate) fn get_parent(&self) -> Vec<Weak<Self>> {
        let parent = match self {
            App { parent, .. } => parent,
            Prod { parent, .. } => parent,
            Abs { parent, .. } => parent,
            BVar { parent, .. } => parent,
            Var { parent, .. } => parent,
            Type => unreachable!(),
            Kind => unreachable!(),
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

    /// Returns `true` if the lnode is [`Prod`].
    ///
    /// [`Prod`]: LNode::Prod
    pub fn is_prod(&self) -> bool {
        matches!(self, Self::Prod { .. })
    }

    pub fn is_sort(&self) -> bool {
        self.is_type() || self.is_kind()
    }

    pub fn is_type(&self) -> bool {
        matches!(self, Self::Type)
    }

    pub fn is_kind(&self) -> bool {
        matches!(self, Self::Type)
    }


    pub fn subs_to(&self, x: Rc<Self>) {
        match self {
            BVar { subs_to, .. } => {
                *subs_to.borrow_mut() = Some(x);
            }

            _ => unreachable!("You can substitute only a bound variable"),
        }
    }

    pub fn unsub(&self) {
        match self {
            BVar { subs_to, .. } => {
                *subs_to.borrow_mut() = None;
            }

            _ => unreachable!("You can substitute only a bound variable"),
        }
    }

    pub fn get_sub(&self) -> Option<Rc<Self>> {
        match self {
            BVar { subs_to, .. } => subs_to.borrow().clone(),

            _ => unreachable!("You can substitute only a bound variable"),
        }
    }
}
