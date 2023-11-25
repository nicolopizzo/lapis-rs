use std::{
    borrow::BorrowMut,
    cell::RefCell,
    collections::{VecDeque, HashMap},
    fmt::{Debug, Write},
    hash::Hash,
    rc::{Rc, Weak},
};

use log::info;
use LNode::*;

use crate::{parser::Rewrite, utils::{deep_clone, get_head, matches}};

#[derive(Clone)]
pub struct NormalForms(pub bool, pub Option<Rc<LNode>>);

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
        ty: RefCell<Option<Rc<Self>>>,
        normal_forms: RefCell<NormalForms>,
        is_meta: bool,
        symb: Option<String>,
    },
    Var {
        is_meta: bool,
        parent: RefCell<Vec<Weak<Self>>>,
        undir: RefCell<Vec<Weak<Self>>>,
        canonic: RefCell<Weak<Self>>,
        building: RefCell<bool>,
        queue: RefCell<VecDeque<Weak<Self>>>,
        ty: RefCell<Option<Rc<Self>>>,
        normal_forms: RefCell<NormalForms>,
        symb: String,
    },
    Type,
    Kind,
}

// Creare una funzione per settare `undir` in cui si trattano ad hoc Type, Kind e Var, togliendo
// undir anche da var.

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
            Abs { bvar, body, .. } => {
                bvar.fmt(f)?;
                if let Some(typ) = bvar.get_type() {
                    f.write_str(": ")?;
                    typ.fmt(f)?;
                }
                f.write_str(" => ")?;
                body.fmt(f)
            }
            App { left, right, .. } => {
                // f.write_str("(")?;
                if left.is_prod() || left.is_abs() {
                    f.write_str("(")?;
                    left.fmt(f)?;
                    f.write_str(")")?;
                } else {
                    left.fmt(f)?;
                }
                f.write_str(" ")?;
                // If on the right I have a substituted bvar, I check the substitution for pretty
                // printing (if I have something other than variables, open parentheses).
                let right = &right.get_sub().unwrap_or(right.clone());
                if !(right.is_bvar() || right.is_var()) {
                    f.write_str("(")?;
                    right.fmt(f)?;
                    f.write_str(")")
                } else {
                    right.fmt(f)
                }
            }
            Prod { bvar, body, .. } => {
                if let BVar { symb, .. } = &**bvar {
                    if symb.is_some() {
                        bvar.fmt(f)?;
                        f.write_str(" : ")?;
                    }
                }
                if let Some(typ) = bvar.get_type() {
                    if typ.is_prod() || typ.is_abs() {
                        f.write_str("(")?;
                        typ.fmt(f)?;
                        f.write_str(")")?;
                    } else {
                        typ.fmt(f)?;
                    }
                }
                f.write_str(" -> ")?;
                body.fmt(f)
            }
            BVar { subs_to, symb, .. } => {
                if let Some(sub) = &*subs_to.borrow() {
                    f.write_str("[")?;
                    sub.fmt(f)?;
                    f.write_str("]")
                } else if let Some(symb) = symb {
                    f.write_str(&symb)
                } else {
                    f.write_str("_")
                }
            }
            Var { symb, .. } => f.write_str(&symb),
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
            Type => (),
            Kind => (),
        }
    }

    pub fn new_app(left: Rc<Self>, right: Rc<Self>) -> Rc<Self> {
        let app = Rc::new(App {
            left: left.clone(),
            right: right.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });

        left.add_parent(app.clone());

        right.add_parent(app.clone());

        app
    }

    pub fn new_prod_unbound(bvar: Rc<Self>, body: Rc<Self>) -> Rc<Self> {
        let prod = Rc::new(Prod {
            bvar: bvar.clone(),
            body: body.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });

        body.add_parent(prod.clone());

        prod
    }

    pub fn new_prod(bvar: Rc<Self>, body: Rc<Self>) -> Rc<Self> {
        let prod = Rc::new(Prod {
            bvar: bvar.clone(),
            body: body.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });

        bvar.bind_to(prod.clone());

        body.add_parent(prod.clone());

        prod
    }

    pub fn new_abs(bvar: Rc<Self>, body: Rc<Self>) -> Rc<Self> {
        let abs = Rc::new(Abs {
            bvar: bvar.clone(),
            body: body.clone(),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
        });

        bvar.bind_to(abs.clone());

        body.add_parent(abs.clone());

        abs
    }

    pub fn new_var(t: Option<Rc<Self>>, symb: &str) -> Rc<Self> {
        Rc::new(Var {
            symb: String::from(symb),
            is_meta: false,
            ty: RefCell::new(t),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
            normal_forms: RefCell::new(NormalForms(false, None)),
        })
    }

    pub fn new_meta_var(t: Option<Rc<Self>>, symb: Option<&str>) -> Rc<Self> {
        Rc::new(BVar {
            symb: symb.map(|s| String::from(s)),
            is_meta: true,
            binder: RefCell::new(Weak::new()),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
            subs_to: RefCell::new(None),
            ty: RefCell::new(t),
            normal_forms: RefCell::new(NormalForms(false, None)),
        })
    }

    pub fn new_bvar(t: Option<Rc<Self>>, symb: Option<&str>) -> Rc<Self> {
        Rc::new(BVar {
            symb: symb.map(|s| String::from(s)),
            is_meta: false,
            binder: RefCell::new(Weak::new()),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
            subs_to: RefCell::new(None),
            ty: RefCell::new(t),
            normal_forms: RefCell::new(NormalForms(false, None)),
        })
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
            Var { ty: t, .. } => t.borrow().clone(),
            BVar { ty: t, .. } => t.borrow().clone(),
            _ => None,
        }
    }

    pub fn infer_as(&self, ty_inf: Rc<Self>) {
        match self {
            Var { ty, .. } => *ty.borrow_mut() = Some(ty_inf),
            BVar { ty, .. } => *ty.borrow_mut() = Some(ty_inf),
            _ => (),
        }
    }

    /// Reset all fields for sharing equality algorithm.
    pub fn reset(&self) {
        self.set_canonic(Weak::new());
        self.set_building(false);
        self.reset_undir();
        self.reset_queue();
        // *self.queue().borrow_mut() = VecDeque::new();
    }

    pub(crate) fn undir(&self) -> Vec<Weak<Self>> {
        match self {
            App { undir, .. }
            | Prod { undir, .. }
            | Abs { undir, .. }
            | BVar { undir, .. }
            | Var { undir, .. } => undir.borrow().to_vec(),
            Type => Vec::new(),
            Kind => Vec::new(),
        }
    }

    pub(crate) fn add_undir(&self, node: &Rc<Self>) {
        match self {
            App { undir, .. }
            | Prod { undir, .. }
            | Abs { undir, .. }
            | BVar { undir, .. }
            | Var { undir, .. } => undir.borrow_mut().push(Rc::downgrade(node)),

            _ => {}
        }
    }

    pub(crate) fn reset_undir(&self) {
        match self {
            App { undir, .. }
            | Prod { undir, .. }
            | Abs { undir, .. }
            | BVar { undir, .. }
            | Var { undir, .. } => *undir.borrow_mut() = Vec::new(),

            _ => {}
        }
    }

    pub(crate) fn reset_queue(&self) {
        match self {
            App { queue, .. }
            | Prod { queue, .. }
            | Abs { queue, .. }
            | BVar { queue, .. }
            | Var { queue, .. } => *queue.borrow_mut() = Vec::new().into(),

            _ => {}
        }
    }

    pub(crate) fn canonic(&self) -> Weak<Self> {
        match self {
            App { canonic, .. }
            | Prod { canonic, .. }
            | Abs { canonic, .. }
            | BVar { canonic, .. }
            | Var { canonic, .. } => canonic.borrow().clone(),

            // The canoic for the sort can only be the sort itself.
            Type => Rc::downgrade(&Rc::new(Type)),
            Kind => Rc::downgrade(&Rc::new(Kind)),
        }
    }

    pub(crate) fn set_canonic(&self, value: Weak<Self>) {
        match self {
            App { canonic, .. }
            | Prod { canonic, .. }
            | Abs { canonic, .. }
            | BVar { canonic, .. }
            | Var { canonic, .. } => *canonic.borrow_mut() = value,

            Type | Kind => (),
        }
    }

    pub(crate) fn building(&self) -> bool {
        match self {
            App { building, .. }
            | Prod { building, .. }
            | Abs { building, .. }
            | BVar { building, .. }
            | Var { building, .. } => *building.borrow(),

            Type | Kind => false,
        }
    }

    pub(crate) fn set_building(&self, b: bool) {
        match self {
            App { building, .. }
            | Prod { building, .. }
            | Abs { building, .. }
            | BVar { building, .. }
            | Var { building, .. } => *building.borrow_mut() = b,
            Type | Kind => (),
        }
    }

    pub(crate) fn queue(&self) -> VecDeque<Weak<Self>> {
        match self {
            App { queue, .. }
            | Prod { queue, .. }
            | Abs { queue, .. }
            | BVar { queue, .. }
            | Var { queue, .. } => queue.borrow().clone(),

            Type | Kind => VecDeque::new(),
        }
    }

    pub(crate) fn push_queue(&self, v: &Rc<Self>) {
        match self {
            App { queue, .. }
            | Prod { queue, .. }
            | Abs { queue, .. }
            | BVar { queue, .. }
            | Var { queue, .. } => queue.borrow_mut().push_back(Rc::downgrade(v)),

            Type | Kind => (),
        }
    }

    pub(crate) fn pop_queue(&self) -> Option<Weak<Self>> {
        match self {
            App { queue, .. }
            | Prod { queue, .. }
            | Abs { queue, .. }
            | BVar { queue, .. }
            | Var { queue, .. } => queue.borrow_mut().pop_front(),

            Type | Kind => None,
        }
    }

    /// Returns the reference to the parent of the current node.
    pub(crate) fn get_parent(&self) -> Vec<Weak<Self>> {
        match self {
            App { parent, .. }
            | Prod { parent, .. }
            | Abs { parent, .. }
            | BVar { parent, .. }
            | Var { parent, .. } => parent.borrow().to_vec(),

            Type | Kind => Vec::new(),
        }
    }

    /// Binds a `BVar` node to an `Abs` node.
    pub(crate) fn bind_to(&self, binder: Rc<LNode>) {
        if !self.is_bvar() || binder.is_abs() {
            // TODO: fail
        }

        let abs = Rc::downgrade(&binder);
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
        matches!(self, Self::Kind)
    }

    pub fn subs_to(&self, x: &Rc<Self>) {
        match self {
            BVar { subs_to, .. } => {
                *subs_to.borrow_mut() = Some(x.clone());
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

            _ => None,
        }
    }
}


pub fn snf(term: &Rc<LNode>, rules: &HashMap<usize, Vec<Rewrite>>) -> Rc<LNode> {
    let term = weak_head(term, rules);
    match &*term {
        LNode::Prod { bvar, body, .. } => {
            let bvar = snf(bvar, rules);
            let body = snf(body, rules);
            LNode::new_prod(bvar, body)
        }
        LNode::Abs { bvar, body, .. } => {
            let bvar = snf(bvar, rules);
            let body = snf(body, rules);
            LNode::new_abs(bvar, body)
        }
        LNode::App { left, right, .. } => {
            let left = snf(left, rules);
            let right = snf(right, rules);
            LNode::new_app(left, right)
        }
        LNode::BVar {
            subs_to,
            normal_forms,
            ..
        } if subs_to.borrow().is_some() => {
            let subs_to = subs_to.borrow().clone().unwrap();
            // TODO: Verifico che ci sia una snf: nel caso in cui c'è la restituisco, altrimenti la
            // calcolo e la salvo.
            let NormalForms(wnf_computed, computed_snf) = normal_forms.borrow().clone();
            if let Some(snf) = computed_snf {
                snf
            } else {
                let snf_term = snf(&subs_to, rules);
                *normal_forms.borrow_mut() = NormalForms(wnf_computed, Some(snf_term.clone()));

                snf_term
            }
        }
        LNode::BVar { ty, .. } => {
            let ty_b = ty.borrow().clone();
            let ty_b = ty_b.map(|ty| snf(&ty, rules));
            *ty.borrow_mut() = ty_b;

            term
        }
        _ => term,
    }
}

pub fn weak_head(node: &Rc<LNode>, rules: &HashMap<usize, Vec<Rewrite>>) -> Rc<LNode> {
    let wnf = match &**node {
        LNode::App { left, right, .. } => {
            // Recursively weaken the head of the application.
            let left = weak_head(left, rules);
            let left = deep_clone(&mut HashMap::new(), &left);

            if let LNode::Abs { bvar, body, .. } = &*left {
                bvar.subs_to(&right);
                weak_head(body, rules)
            } else {
                // Sono già in normal form.
                let right = weak_head(right, rules);
                LNode::new_app(left, right)
            }
        }
        LNode::BVar {
            subs_to,
            normal_forms,
            ..
        } if subs_to.borrow().is_some() => {
            let NormalForms(wnf_computed, snf) = normal_forms.borrow().clone();
            if wnf_computed {
                subs_to.borrow().clone().unwrap()
            } else {
                let subs = subs_to.borrow().clone().unwrap();
                let wnf = weak_head(&subs, rules);
                *normal_forms.borrow_mut() = NormalForms(true, snf);
                *subs_to.borrow_mut() = Some(wnf.clone());
                wnf
            }
        }
        _ => node.clone(),
    };

    let head = get_head(&wnf);
    let head_ptr = Rc::into_raw(head.clone()) as usize;

    // For each possible rewrite rule, check if `wnf` matches with `lhs`. If `wnf` cannot be
    // rewritten to anything, the for is skipped (`&Vec::new()`) and `wnf` is returned.
    let rew = rules.get(&head_ptr);
    if let Some(rew) = rew {
        for Rewrite(lhs, rhs) in rew {
            let mut subs = HashMap::new();
            let lhs = deep_clone(&mut subs, &lhs);
            let rhs = deep_clone(&mut subs, &rhs);

            // Mi mantengo un campo booleano per le metavariabili
            if matches(&wnf, &lhs, rules) {
                return weak_head(&rhs, rules);
            }
        }
    }

    wnf
}
