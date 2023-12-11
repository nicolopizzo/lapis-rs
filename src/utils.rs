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

/// Verifies that `term` matches `lhs` up to weakening.
/// `pattern` is the left hand side of a rewrite rule, so it can only be `{ App, Var, BVar, Abs }`.
/// `term` must be in whnf.
pub fn matches(term: &Rc<LNode>, pattern: &Rc<LNode>, rules: &RewriteMap) -> bool {
    match (&**term, &**pattern) {
        (
            LNode::App {
                left: l1,
                right: r1,
                ..
            },
            LNode::App {
                left: l2,
                right: r2,
                ..
            },
        ) => {
            // Il match avviene a meno di whnf.
            let l1 = weak_head(&l1, rules);
            let r1 = weak_head(&r1, rules);

            let b1 = matches(&l1, &l2, rules);
            let b2 = matches(&r1, &r2, rules);
            b1 && b2
        }

        /*
         * 1. Devo distinguere metavariabili da variabili bound. Le variabili bound non si
         *    istanziano.
         * 2. Se è una metavar già istanziata => verifico l'alpha-eq tra termine e sostituito.
         * 3. Se è bound (variabile in lambda) deve essre bound dall'altra. Verifico con binder()
         *    il match dei binder. In questo caso non li istanzio. Faccio puntare un puntatore con
         *    .canonic() i binder.
         * */
        (LNode::BVar { subs_to, .. }, _) if subs_to.borrow().is_some() => {
            match &*subs_to.borrow() {
                Some(subs) => matches(subs, pattern, rules),
                None => unreachable!(),
            }
        }

        (_, LNode::BVar { subs_to, .. }) if subs_to.borrow().is_some() => {
            match &*subs_to.borrow() {
                Some(subs) => matches(term, subs, rules),
                None => unreachable!(),
            }
        }
        (
            tterm,
            LNode::BVar {
                subs_to,
                is_meta,
                binder: p_binder,
                ..
            },
        ) => {
            // occur_check(metavar, term); ==> verifica che nel termine non ci sia metavar.
            // se il check fallisce => panic();
            if *is_meta {
                *subs_to.borrow_mut() = Some(term.clone());

                true
            } else {
                if let LNode::BVar {
                    binder: tbinder, ..
                } = tterm
                {
                    let c1 = tbinder.borrow().upgrade();
                    let c2 = p_binder.borrow().upgrade();
                    c1 == c2
                } else {
                    false
                }
            }
        }
        (
            LNode::Prod {
                bvar: l1, body: b1, ..
            },
            LNode::Prod {
                bvar: l2, body: b2, ..
            },
        ) => matches(&l1, &l2, rules) && matches(&b1, &b2, rules),
        (
            LNode::Abs {
                bvar: l1, body: b1, ..
            },
            LNode::Abs {
                bvar: l2, body: b2, ..
            },
        ) => matches(&l1, &l2, rules) && matches(&b1, &b2, rules),
        // Constant variables, sorts.
        _ => term == pattern,
    }
}
