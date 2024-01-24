use std::{
    borrow::BorrowMut,
    cell::RefCell,
    collections::{HashMap, VecDeque},
    fmt::{Debug, Write},
    hash::Hash,
    rc::{Rc, Weak},
};

use log::info;
use LNode::*;

use deepsize::*;

use crate::{
    debug,
    parser::{Rewrite, RewriteMap},
    utils::{deep_clone, get_head, matches},
};

#[derive(Clone,DeepSizeOf)]
pub struct NormalForms(pub bool, pub Option<Rc<LNode>>);

/// Enum representing a lambda node. Such node can have three forms:
/// - Application: an application node has two children.
/// - Abstraction: an abstraction node has one child.
/// - Variable: this kind of node can represent bound and unbound variables.
#[derive(Clone,DeepSizeOf)]
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
                    f.write_str(symb)
                } else {
                    f.write_str("_")
                }
            }
            Var { symb, .. } => f.write_str(symb),
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

    //CSC: alla bvar non aggiungo il parent?
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

        //CSC: alla bvar non aggiungo il parent?
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

    pub fn new_var(ty: Option<Rc<Self>>, symb: &str) -> Rc<Self> {
        let term = Rc::new(Var {
            symb: String::from(symb),
            is_meta: false,
            ty: RefCell::new(ty),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
            normal_forms: RefCell::new(NormalForms(false, None)),
        });

        term.set_canonic(Rc::downgrade(&term));

        term
    }

    pub fn new_meta_var(ty: Option<Rc<Self>>, symb: Option<&str>) -> Rc<Self> {
        Rc::new(BVar {
            symb: symb.map(String::from),
            is_meta: true,
            binder: RefCell::new(Weak::new()),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
            subs_to: RefCell::new(None),
            ty: RefCell::new(ty),
            normal_forms: RefCell::new(NormalForms(false, None)),
        })
    }

    pub fn new_bvar(ty: Option<Rc<Self>>, symb: Option<&str>) -> Rc<Self> {
        Rc::new(BVar {
            symb: symb.map(String::from),
            is_meta: false,
            binder: RefCell::new(Weak::new()),
            parent: RefCell::new(Vec::new()),
            undir: RefCell::new(Vec::new()),
            canonic: RefCell::new(Weak::new()),
            building: RefCell::new(false),
            queue: RefCell::new(Vec::new().into()),
            subs_to: RefCell::new(None),
            ty: RefCell::new(ty),
            normal_forms: RefCell::new(NormalForms(false, None)),
        })
    }

    pub(crate) fn is_abs(&self) -> bool {
        matches!(self, Abs { .. })
    }

    pub(crate) fn is_bvar(&self) -> bool {
        matches!(self, BVar { .. })
    }

    pub(crate) fn is_flexible(&self) -> bool {
        if let BVar { is_meta, subs_to, .. } = self {
            *is_meta && subs_to.borrow().is_none()
        } else { false }
    }

    pub(crate) fn is_var(&self) -> bool {
        matches!(self, Var { .. })
    }

    pub(crate) fn is_app(&self) -> bool {
        matches!(self, App { .. })
    }

    pub fn get_type(&self) -> Option<Rc<Self>> {
        match self {
            Var { ty, .. } => ty.borrow().clone(),
            BVar { ty, .. } => ty.borrow().clone(),
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
    }

    //CSC: nome fuorviante; ridenominare in arity e farla 0-based!
    pub fn size(&self) -> usize {
        match self {
            BVar { subs_to, .. } => {
                let subs = &*subs_to.borrow();
                match subs {
                    Some(sub) => sub.size(),
                    None => 1,
                }
            }
            Var { .. } | Type | Kind => 1,
            App { left, .. } => left.size() + 1,
            Prod { .. } | Abs { .. } => 1,
        }
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

            //CSC: meglio abortire?
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

            //CSC: bug qui?
            Type | Kind => Vec::new(),
        }
    }

    /// Binds a `BVar` node to an `Abs` node.
    pub(crate) fn bind_to(&self, binder: Rc<LNode>) {
        let abs = Rc::downgrade(&binder);
        if let BVar { binder, .. } = self {
            *binder.borrow_mut() = abs
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
            App { left, right, .. } => {
                left.unsub();
                right.unsub()
            }
            Prod { bvar, body, .. } | Abs { bvar, body, .. } => {
                bvar.unsub();
                body.unsub()
            }

            _ => (),
        }
    }

    pub fn unsub_meta(&self) {
        match self {
            BVar {
                subs_to, is_meta, ..
            } => {
                if *is_meta {
                    *subs_to.borrow_mut() = None;
                }
            }
            App { left, right, .. } => {
                left.unsub();
                right.unsub()
            }
            Prod { bvar, body, .. } | Abs { bvar, body, .. } => {
                bvar.unsub();
                body.unsub()
            }

            _ => (),
        }
    }
    pub fn get_sub(&self) -> Option<Rc<Self>> {
        match self {
            BVar { subs_to, .. } => subs_to.borrow().clone(),

            _ => None,
        }
    }

    pub fn bind_to_context(&self) {
        if let BVar { binder, .. } = self {
            *binder.borrow_mut() = Weak::new()
        }
    }

    pub fn is_meta(&self) -> bool {
        match self {
            LNode::BVar { is_meta, .. } => *is_meta,
            _ => false,
        }
    }
}

pub fn snf(term: &Rc<LNode>, rules: &RewriteMap) -> Rc<LNode> {
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
            computed_snf.unwrap_or_else(|| {
                let snf_term = snf(&subs_to, rules);
                *normal_forms.borrow_mut() = NormalForms(wnf_computed, Some(snf_term.clone()));

                snf_term
            })
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

pub fn weak_head(node: &Rc<LNode>, rules: &RewriteMap) -> Rc<LNode> {
    let wnf = match &**node {
        LNode::App { left, right, .. } => {
            // Recursively weaken the head of the application.
            let left = weak_head(left, rules);
            // CSC: tante deep_clone
            let left = deep_clone(&mut HashMap::new(), &left);

            if let LNode::Abs { bvar, body, .. } = &*left {
                bvar.subs_to(right);
                weak_head(body, rules)
            } else {
                LNode::new_app(left, right.clone())
            }
        }
        LNode::BVar {
            subs_to,
            normal_forms,
            ..
        } => {
            let subs = &mut *subs_to.borrow_mut();
            match subs {
                Some(sub) => {
                    let NormalForms(wnf_computed, snf) = normal_forms.borrow().clone();
                    if wnf_computed {
                        sub.clone()
                    } else {
                        let wnf = weak_head(sub, rules);
                        *normal_forms.borrow_mut() = NormalForms(true, snf);
                        *subs = Some(wnf.clone());
                        wnf
                    }
                }
                None => node.clone(),
            }
        }
        _ => node.clone(),
    };

    rewrite_to(&wnf, rules).unwrap_or(wnf)
}

fn rewrite_to(wnf: &Rc<LNode>, rules: &RewriteMap) -> Option<Rc<LNode>> {
    let head = get_head(wnf);
    let size = wnf.size();
    let head_ptr = Rc::into_raw(head.clone()) as usize;

    let key = (head_ptr, size);

    // For each possible rewrite rule, check if `wnf` matches with `lhs`. If `wnf` cannot be
    // rewritten to anything, the for is skipped (`&Vec::new()`) and `wnf` is returned.
    let rew = rules.get(&key);
    if let Some(rew) = rew {
        for Rewrite(lhs, rhs) in rew {
            let mut subs = HashMap::new();
            let lhs = deep_clone(&mut subs, lhs);
            let rhs = deep_clone(&mut subs, rhs);

            // Mi mantengo un campo booleano per le metavariabili
            if matches(wnf, &lhs, rules) {
                return Some(weak_head(&rhs, rules));
            }
        }
    }

    None
}
