#![allow(unused_variables)]
use core::panic;
use std::{
    collections::HashMap,
    fmt::format,
    hash::Hash,
    rc::{self, Rc},
};

use crate::{lgraph::LGraph, lnode::LNode, parser::Context};

fn deep_clone(subs: &mut HashMap<usize, Rc<LNode>>, node: Rc<LNode>) -> Rc<LNode> {
    let node_ptr = Rc::into_raw(node.clone()) as usize;

    // Se ho già incontrato questo nodo, restituisco quello che ha preso il suo posto.
    if let Some(x) = subs.get(&node_ptr) {
        x.clone()
    } else {
        let new_node = match node.as_ref() {
            LNode::App { left, right, .. } => {
                let left_new = deep_clone(subs, left.clone());
                let right_new = deep_clone(subs, right.clone());
                if left_new == *left && right_new == *right {
                    return node.clone();
                }

                LNode::new_app(left_new, right_new)
            }
            LNode::Prod { bvar, body, .. } => {
                let bvar_new = deep_clone(subs, bvar.clone());
                let body_new = deep_clone(subs, body.clone());
                if bvar_new == *bvar && bvar_new == *bvar {
                    return node.clone();
                }

                LNode::new_prod(bvar_new, body_new)
            }
            LNode::Abs { bvar, body, .. } => {
                let bvar_new = deep_clone(subs, bvar.clone());
                let body_new = deep_clone(subs, body.clone());
                if bvar_new == *bvar && bvar_new == *bvar {
                    return node.clone();
                }

                LNode::new_abs(bvar_new, body_new)
            }

            LNode::BVar { subs_to, .. } => {
                let sub = subs_to.borrow();
                if sub.is_some() {
                    // Se c'è una sostituzione esplicita effettuo sharing
                    node.clone()
                } else {
                    Rc::new(node.as_ref().clone())
                }
            }

            // Var, Type and Kind can be shared
            _ => node.clone(),
        };
        subs.insert(node_ptr, new_node.clone());

        new_node
    }
}

fn weak_head(node: Rc<LNode>) -> Rc<LNode> {
    match node.as_ref() {
        LNode::App { left, right, .. } => {
            // Recursively weaken the head of the application.
            let left = weak_head(left.clone());
            let left = deep_clone(&mut HashMap::new(), left);

            if let LNode::Abs { bvar, body, .. } = left.as_ref().clone() {
                bvar.subs_to(right.clone());
                return body.clone();
            } else {
                panic!();
            }
        }
        _ => node.clone(),
    }
}

fn equality_check(r1: Rc<LNode>, r2: Rc<LNode>) -> bool {
    let g = LGraph::from_roots(r1, r2);
    let check_res = g.blind_check();
    if check_res.is_err() {
        return false;
    } else {
        g.var_check()
    }

    /* Controllo che i campi `undir`, `canonic`, etc... siano resettati? Oppure non serve? */
}

/// Verifies that inferring the type of `node` reduces to `typ_exp`.
fn type_check(node: Rc<LNode>, typ_exp: Rc<LNode>) {
    match node.as_ref().clone() {
        LNode::Abs { bvar, body, .. } => {
            let bvar_ty = bvar.get_type();
            let typ_exp = weak_head(typ_exp);
            if let LNode::Prod {
                bvar: a,
                body: body_ty,
                ..
            } = typ_exp.as_ref().clone()
            {
                if let Some(typ) = bvar_ty {
                    // TODO: if `typ` is not convertible to `typ_exp`, fail.
                } else {
                    bvar.infer_as(a);
                }

                type_check(body, body_ty);
            } else {
                panic!("Error: `typ_exp` in weak head normal form is not a `LNode::Prod`");
            }
        }
        LNode::Var { ty, .. } if ty.borrow().is_none() => {
            *ty.borrow_mut() = Some(typ_exp);
        }
        _ => {
            let typ_inf = type_infer(node).expect("Error: could not infer type for `lhs`.");
            // TODO: if `typ_inf` is not convertible to `typ_exp`, fail.
            // Add here alpha equivalence between `typ_inf` and `typ_exp`.
            // if !equality_check(typ_inf.clone(), typ_exp.clone()) {
            // panic!("Error in eq_check");
            // }
        }
    }
}

fn check_wkhd<F>(node: Rc<LNode>, pred: F)
where
    F: Fn(Rc<LNode>) -> bool,
{
    let node = type_infer(node).unwrap();
    let node = weak_head(node);
    assert!(pred(node));
}

fn check_rule(lhs: Rc<LNode>, rhs: Rc<LNode>) {
    let lhs_typ = type_infer(lhs.clone());
    if let Some(lhs_typ) = lhs_typ {
        type_check(rhs, lhs_typ);
    } else {
        let rhs_typ = type_infer(rhs.clone());
        if let Some(rhs_typ) = rhs_typ {
            type_check(lhs, rhs_typ);
        } else {
            println!(
                "[ WARN ] Could need unification for {:?} --> {:?}",
                lhs, rhs
            );
        }
    }
}

fn type_infer(node: Rc<LNode>) -> Option<Rc<LNode>> {
    match node.as_ref() {
        LNode::App { left, right, .. } => {
            let left_ty = type_infer(left.clone()).unwrap();

            let left_whd = weak_head(left_ty.clone());

            // Copio ricorsivamente il grafo, ma sharare le sostituzioni esplicite già esistenti
            // Posso anche sharare le parti dell'albero che non contengono `BVar`.
            let left_whd = deep_clone(&mut HashMap::new(), left_whd.clone());

            if let LNode::Prod { bvar, body, .. } = left_whd.as_ref() {
                assert!(bvar.is_bvar(), "`left` node in `Prod` is not a `BVar`.");

                // check equality between left and `right_ty`
                let bvar_ty = bvar.get_type().expect("BVar must be typed in Product");
                type_check(right.clone(), bvar_ty);

                // substitute occurrences of `bvar` in `body` with `right`
                bvar.subs_to(right.clone());
                return Some(body.clone());
            } else {
                panic!("Error: `left` in `App` node is not evaluated to a `Prod`.")
            }
        }
        LNode::Abs { bvar, body, .. } => {
            assert!(
                bvar.is_bvar(),
                "`bvar` in `Abs` node is not a bounded variable."
            );

            let bvar_ty = bvar.get_type();
            if bvar_ty.is_none() {
                return None;
            }
            let bvar_ty = bvar_ty.unwrap();
            check_wkhd(bvar_ty, |node| node.is_type());

            let body_ty = type_infer(body.clone()).unwrap();
            check_wkhd(body_ty.clone(), |node| node.is_sort());

            Some(LNode::new_prod(bvar.clone(), body_ty.clone()))
        }
        LNode::BVar { .. } => node.get_type(),
        LNode::Var { .. } => node.get_type(),
        LNode::Prod { bvar, body, .. } => {
            assert!(
                bvar.is_bvar(),
                "`bvar` in `Prod` node is not a bounded variable."
            );

            let bvar_ty = bvar.get_type().expect("Variable is not typed.");
            check_wkhd(bvar_ty, |node| node.is_type());

            let body_ty = type_infer(body.clone()).unwrap();
            check_wkhd(body_ty.clone(), |node| node.is_sort());

            Some(body_ty)
        }
        LNode::Type => Some(Rc::new(LNode::Kind)),
        LNode::Kind => unreachable!("Tried to type `Kind` sort."),
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::{parse, print_context, Rewrite};

    use super::*;
    use std::{collections::HashSet, env, fmt::format, fs, rc::Rc};

    fn before_each() {
        env::set_current_dir("examples").expect("Could not set directory");
    }

    fn after_each() {
        env::set_current_dir("..").expect("Could not set dir");
    }

    #[test]
    fn test_simple() {
        before_each();
        let file_path = "nat.dk";
        let c = parse(String::from(file_path));

        let Context(gamma, rules) = c;
        print_context(&gamma);

        for (idx, Rewrite(lhs, rhs)) in (1..).zip(rules.into_iter()) {
            println!("Trying to type rule#{}", idx);
            check_rule(lhs, rhs);
        }

        after_each();
        // println!("{:?}", env::current_dir());
    }

    #[test]
    fn test_all() {
        before_each();
        let file_path = "cic.dk";
        let c = parse(String::from(file_path));
        let Context(gamma, rules) = c;
        print_context(&gamma);

        for (key, value) in &gamma {
            if let Some(value) = value.clone() {
                let ty = type_infer(value);
                //println!("{key: >8} --> {:p}");
            }
        }

        for Rewrite(lhs, rhs) in rules {
            check_rule(lhs, rhs);
        }

        after_each();
    }

    #[test]
    fn test_context() {
        before_each();
        let file_path = "nat.dk";
        let c = parse(String::from(file_path));

        let Context(gamma, _) = c;
        print_context(&gamma);

        let typ_gamma = gamma
            .iter()
            .map(|(key, opt)| (key.clone(), opt.clone().unwrap().get_type()))
            .collect();
        print_context(&typ_gamma);
        // for (key, node) in &typ_gamma {
        // if let Some(node) = node.clone() {
        // let node_typ = type_infer(node);
        // if let Some(node_typ) = node_typ {
        // println!("{key: >10} --> {node_typ:p}");
        // }
        // } else {
        // println!("{key: >10} --> None");
        // }
        // }
    }

    #[test]
    fn test_dependant() {
        before_each();
        let file_path = "vec.dk";
        let Context(gamma, rules) = parse(String::from(file_path));

        let append = gamma.get("append").unwrap();
        let Rewrite(lhs, rhs) = rules[3].clone();

        let lhs_ty = type_infer(lhs);
        let rhs_ty = type_infer(rhs.clone());
        dbg!(&rhs);
        dbg!(&rhs_ty);
    }
}
