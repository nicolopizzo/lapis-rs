use std::{collections::HashMap, rc::Rc};

use crate::{
    lnode::{weak_head, LNode},
    parser::{Rewrite, RewriteMap},
};

#[macro_export]
macro_rules! debug {
    ( $fun: expr ) => {{
        info!(target: "FOLDING", "{{{{{{");
        // unsafe { OPEN_DEBUG += 1 }
        let res = $fun;
        // unsafe { OPEN_DEBUG -= 1 }
        info!(target: "FOLDING", "}}}}}}");
        res
    }};


    ( $fun: expr, $target: expr ) => {{
        info!(target: $target, "{{{{{{");
        // unsafe { OPEN_DEBUG += 1 }
        let res = $fun;
        // unsafe { OPEN_DEBUG -= 1 }
        info!(target: $target, "}}}}}}");
        res
    }};
}

pub fn get_head(term: &Rc<LNode>) -> &Rc<LNode> {
    match &**term {
        LNode::App { left, .. } => get_head(left),
        _ => term,
    }
}

pub fn deep_clone(subs: &mut HashMap<usize, Rc<LNode>>, node: &Rc<LNode>) -> Rc<LNode> {
    let node_ptr = Rc::into_raw(node.clone()) as usize;

    // Se ho già incontrato questo nodo, restituisco quello che ha preso il suo posto.
    if let Some(x) = subs.get(&node_ptr) {
        x.clone()
    } else {
        let new_node = match &**node {
            LNode::App { left, right, .. } => {
                let left_new = deep_clone(subs, left);
                let right_new = deep_clone(subs, right);
                if left_new == *left && right_new == *right {
                    return node.clone();
                }

                LNode::new_app(left_new, right_new)
            }
            LNode::Prod { bvar, body, .. } => {
                let bvar_new = deep_clone(subs, bvar);
                let body_new = deep_clone(subs, body);
                if bvar_new == *bvar && body_new == *body {
                    return node.clone();
                }

                LNode::new_prod(bvar_new, body_new)
            }
            LNode::Abs { bvar, body, .. } => {
                let bvar_new = deep_clone(subs, bvar);
                let body_new = deep_clone(subs, body);
                if bvar_new == *bvar && body_new == *body {
                    return node.clone();
                }

                LNode::new_abs(bvar_new, body_new)
            }

            LNode::BVar {
                subs_to,
                ty,
                symb,
                is_meta,
                ..
            } => {
                let sub = &subs_to.borrow();
                if sub.is_some() {
                    // Se c'è una sostituzione esplicita effettuo sharing
                    node.clone()

                } else {
                    // Deep cloning the Type
                    let ty = ty.borrow().clone();
                    let ty = ty.map(|ty| deep_clone(subs, &ty));

                    let symb = symb.as_deref();
                    if *is_meta {
                        LNode::new_meta_var(ty, symb)
                    } else {
                        // Must share bvar???
                        LNode::new_bvar(ty, symb)
                    }
                }
            }

            // Var, Type and Kind can be shared
            _ => node.clone(),
        };
        subs.insert(node_ptr, new_node.clone());

        new_node
    }
}

// Returns the new head and updates args in place
// It does not open substituted vars to allow to record the wnf
fn decompose(term: &Rc<LNode>, args: Vec<Rc<LNode>>) -> &Rc<LNode> {
    let mut head = term;
    while let LNode::App {left, right, ..} = &**head => {
        args.push(*right);
        head = left;
    }
    head
}
///
/// Verifies that `term` matches `lhs` up to weakening.
/// `pattern` is the left hand side of a rewrite rule, so it can only be `{ App, Var, BVar, Abs }`.
/// `term` must be in whnf, unless we know that the pattern is an uninstantiated meta-variable
/// `pattern` must be in whnf nelle regole di riscrittura
pub fn matches(term: &Rc<LNode>, args: Vec<Rc<LNode>>, pattern: &Rc<LNode>, rules: &RewriteMap) -> Option<Vec<Rc<LNode>>> {
    let (phead, pargs) = decompose(pattern);
    matches_aux(term, args, phead, pargs, rules)
}

/// Verifies that `term` matches `lhs` up to weakening.
/// `pattern` is the left hand side of a rewrite rule, so it can only be `{ App, Var, BVar, Abs }`.
/// `term` must be in whnf, unless we know that the pattern is an uninstantiated meta-variable
/// `pattern` must be in whnf nelle regole di riscrittura
pub fn matches_aux(term: &Rc<LNode>, args: Vec<Rc<LNode>>, phead: &Rc<LNode>, pargs: Vec<Rc<LNode>>, rules: &RewriteMap) -> Option<Vec<Rc<LNode>>> {
    match (&**term, &**phead) {
        (LNode::BVar { subs_to, .. }, _) if subs_to.borrow().is_some() => {
            match &*subs_to.borrow() {
                Some(subs) => QUI DEVO FARE DECOMPOSE! MA SE SONO COME INVARIANTE IN WHD QUESTO CASO NON SERVE! matches_aux(subs, args, phead, pargs, rules),
                None => unreachable!(),
            }
        }
        (
            _,
            LNode::BVar {
                subs_to,
                is_meta,
                ..
            },
        ) => {
            XXX: cattura tutti gli args e amen
            // occur_check(metavar, term); ==> verifica che nel termine non ci sia metavar.
            // se il check fallisce => panic();
            if *is_meta {
                *subs_to.borrow_mut() = Some(term.clone());

                true
            } else {
                Rc::ptr_eq(term,pattern)
            }
        }
        (LNode::Prod { bvar: l1, body: b1, ..  }, LNode::Prod { bvar: l2, body: b2, ..  }
        ) => { assert!(args.is_empty() && pargs.is_empty()); TERMINI NON IN WHD! matches(&l1, &l2, rules) && matches(&b1, &b2, rules) },
        (LNode::Abs { bvar: l1, body: b1, ..  }, LNode::Abs { bvar: l2, body: b2, ..  }
        ) => { assert!(args.is_empty() && pargs.is_empty()); TERMINI NON IN WHD! matches(&l1, &l2, rules) && matches(&b1, &b2, rules) },
        (LNode::Type, LNode::Type) => { assert!(args.is_empty() && pargs.is_empty()); true },
        (LNode::Kind, LNode::Kind) => { assert!(args.is_empty() && pargs.is_empty()); true },
        // Variables
        _ => { assert!(pargs.is_empty()); Rc::ptr_eq(term,pattern) }
    }

    if arg.len() < parg.len() { return None };
    for (arg, parg) in args.iter().zip(pargs.iter()) {
        let res =if parg.is_flexible() {
            matches(r1, &r2, rules)
        } else {
            //info!("### NON FLEXIBLE PATTERN {:?} FORCING EVALUATION OF {:?}", r2, r1);
            let arg = weak_head(&arg, rules);
            matches(&arg, Vec::new(), &parg, rules)
        };
        assert!(res.is_empty());
    }
}
