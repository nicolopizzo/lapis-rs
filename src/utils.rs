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

                let res = LNode::new_prod(bvar_new.clone(), body_new);
                bvar_new.bind_to(&res);
                res
            }
            LNode::Abs { bvar, body, .. } => {
                let bvar_new = deep_clone(subs, bvar);
                let body_new = deep_clone(subs, body);
                if bvar_new == *bvar && body_new == *body {
                    return node.clone();
                }

                let res = LNode::new_abs(bvar_new.clone(), body_new);
                bvar_new.bind_to(&res);
                res
            }

            LNode::Var {
                subs_to,
                ty,
                symb,
                is_meta,
                binder,
                ..
            } => {
                let sub = &subs_to.borrow();
                if sub.is_some() ||
                   (!is_meta && binder.borrow().upgrade().is_none()) {
                    // Se c'è una sostituzione o è una variabile libera
                    // effettuo sharing
                    node.clone()

                } else {
                    // Deep cloning the Type
                    let ty = ty.borrow().clone();
                    let ty = ty.map(|ty| deep_clone(subs, &ty));

                    let symb = symb.as_deref();
                    if *is_meta {
                        LNode::new_meta_var(ty, symb)
                    } else {
                        LNode::new_var(ty, symb)
                    }
                }
            }

            // Type and Kind can be shared
            _ => node.clone(),
        };
        subs.insert(node_ptr, new_node.clone());

        new_node
    }
}

/// Verifies that `term` matches `lhs` up to weakening.
/// `pattern` is the left hand side of a rewrite rule, so it can only be `{ App, Var, BVar, Abs }`.
/// `term` must be in whnf, unless we know that the pattern is an uninstantiated meta-variable
/// `pattern` must be in whnf nelle regole di riscrittura
pub fn matches(term: &Rc<LNode>, pattern: &Rc<LNode>, rules: &RewriteMap) -> bool {
    let res =
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
            let b1 = matches(&l1, &l2, rules);

            let b2 = if r2.is_flexible() {
                matches(r1, &r2, rules)
            } else {
                //info!("### NON FLEXIBLE PATTERN {:?} FORCING EVALUATION OF {:?}", r2, r1);
                let r1 = weak_head(&r1, rules);
                matches(&r1, &r2, rules)
            };
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
        (LNode::Var { subs_to, .. }, _) if subs_to.borrow().is_some() => {
            match &*subs_to.borrow() {
                Some(subs) => matches(subs, pattern, rules),
                None => unreachable!(),
            }
        }

        (_, LNode::Var { subs_to, .. }) if subs_to.borrow().is_some() => {
            match &*subs_to.borrow() {
                Some(subs) => matches(term, subs, rules),
                None => unreachable!(),
            }
        }
        (
            _,
            LNode::Var {
                subs_to,
                is_meta,
                ..
            },
        ) => {
            // occur_check(metavar, term); ==> verifica che nel termine non ci sia metavar.
            // se il check fallisce => panic();
            if *is_meta {
                *subs_to.borrow_mut() = Some(term.clone());

                true
            } else {
                let res = Rc::ptr_eq(term,pattern);
                //if !res { println!("VAR/VAR FAILURE: {:?}", std::ptr::eq(term,pattern)); };
                res
            }
        }
        ( LNode::Prod { bvar: bvar1, body: body1, ..  },
          LNode::Prod { bvar: bvar2, body: body2, ..  } )
      | ( LNode::Abs { bvar: bvar1, body: body1, ..  },
          LNode::Abs { bvar: bvar2, body: body2, ..  },) => {
            //CSC: Code cut&paste from conversion and other places
            let LNode::Var { ty: ty1, .. } = &**bvar1 else { panic!("Not a Var") };
            let LNode::Var { ty: ty2, .. } = &**bvar2 else { panic!("Not a Var") };
            (ty2.borrow().as_ref().is_none() ||
             matches(ty1.borrow().as_ref().unwrap(),
                      ty2.borrow().as_ref().unwrap(),
                      rules))
            &&
                {
                    bvar1.bind_to_context();
                    bvar2.bind_to_context();
                    bvar2.subs_to(bvar1);
                    let res = matches(&body1, &body2, rules);
                    bvar2.unsub();
                    bvar2.bind_to(&pattern);
                    bvar1.bind_to(&term);
                    res
                }
          }
        // Constant variables, sorts.
        (LNode::Type, LNode::Type) => true,
        (LNode::Kind, LNode::Kind) => true,
        _ => Rc::ptr_eq(term,pattern)
    }
    //; if !res { println!("MATCH FAILURE: {:?} === {:?}", term, pattern); }; res
    ; res
}
