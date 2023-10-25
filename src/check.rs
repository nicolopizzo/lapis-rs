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

fn type_check(node: Rc<LNode>) -> Rc<LNode> {
    match node.as_ref() {
        LNode::App { left, right, .. } => {
            let left_ty = type_check(left.clone());
            let right_ty = type_check(right.clone());

            let left_whd = weak_head(left_ty.clone());

            // Copio ricorsivamente il grafo, ma sharare le sostituzioni esplicite già esistenti
            // Posso anche sharare le parti dell'albero che non contengono `BVar`.
            let right_ty = deep_clone(&mut HashMap::new(), right_ty.clone());
            let left_whd = deep_clone(&mut HashMap::new(), left_whd.clone());

            if let LNode::Prod { bvar, body, .. } = left_whd.as_ref() {
                assert!(bvar.is_bvar(), "`left` node in `Prod` is not a `BVar`.");

                // check equality between left and `right_ty`
                // TODO: uncomment for sharing equality
                // let bvar_ty = bvar.get_type().expect("Bvar is untyped");
                // equality_check(bvar_ty.clone(), right_ty.clone());

                // substitute occurrences of `bvar` in `body` with `right`
                bvar.subs_to(right.clone());
                return body.clone();
            } else {
                panic!("Error: `left` in `App` node is not evaluated to a `Prod`.")
            }
        }
        LNode::Abs { bvar, body, .. } => {
            assert!(
                bvar.is_bvar(),
                "`bvar` in `Abs` node is not a bounded variable."
            );
            let bvar_ty = bvar.get_type().expect("Variable is not typed.");
            let bvar_ty = type_check(bvar_ty.clone());
            let bvar_ty = weak_head(bvar_ty);
            assert!(bvar_ty.is_type());

            let body_ty = type_check(body.clone());
            let body_ty = weak_head(body_ty);

            let body_ty_sort = type_check(body_ty.clone());
            let body_ty_sort = weak_head(body_ty_sort);
            assert!(body_ty_sort.is_sort());

            LNode::new_prod(bvar.clone(), body_ty.clone())
        }
        LNode::BVar { ty, .. } => ty.clone().expect("Variable is not typed."),
        LNode::Var { ty, .. } => ty.clone().expect("Variable is not typed."),
        LNode::Prod { bvar, body, .. } => {
            assert!(
                bvar.is_bvar(),
                "`bvar` in `Prod` node is not a bounded variable."
            );

            let bvar_ty = bvar.get_type().expect("Variable is not typed.");
            let bvar_ty = type_check(bvar_ty.clone());
            let bvar_ty = weak_head(bvar_ty);
            assert!(bvar_ty.is_type());

            let body_ty = type_check(body.clone());
            let body_ty = weak_head(body_ty);
            assert!(body_ty.is_sort());

            body_ty
        }
        LNode::Type => Rc::new(LNode::Kind),
        LNode::Kind => unreachable!("Tried to type `Kind` sort."),
    }
}
mod tests {
    use crate::parser::{parse, print_context, Rewrite};

    use super::*;
    use std::{collections::HashSet, env, fmt::format, fs, rc::Rc};

    fn setup() {
        env::set_current_dir("examples").expect("Could not set directory");
    }

    #[test]
    fn test_simple() {
        setup();
        let file_path = "nat.dk";
        let c = parse(String::from(file_path));

        print_context(&c);
        let Context(gamma, rules) = c;

        for (idx, Rewrite(lhs, rhs)) in (1..).zip(rules.into_iter()) {
            let lhs_ty = type_check(lhs);
            let rhs_ty = type_check(rhs);
            println!("Rule#{}", idx);
            println!("lhs: {:p}, rhs: {:p}\n", lhs_ty, rhs_ty)
        }
    }

    #[test]
    fn test_all() {
        setup();
        let file_path = "cic.dk";
        let c = parse(String::from(file_path));
        print_context(&c);
        let Context(gamma, _) = c;

        for (key, value) in &gamma {
            // `Kind` sort is always well formed.
            if key == "Kind" {
                continue;
            }
            let ty = type_check(value.clone());
            println!("{key: >8} --> {ty:p}");
        }
    }

    #[test]
    fn test_context() {
        setup();
        let file_path = "nat.dk";
        let c = parse(String::from(file_path));

        print_context(&c);
        let Context(gamma, _) = c;

        let typ_gamma = gamma
            .iter()
            .map(|(key, value)| (key.clone(), type_check(value.clone())))
            .collect();
        print_context(&Context(typ_gamma, Vec::default()));
        // for (key, value) in &gamma {
        //     let ty = type_check(value.clone());
        //     println!("{key: >10} --> {ty:p}");
        // }
    }

    #[test]
    fn test_dependant() {
        setup();
        let file_path = "vec.dk";
        let Context(gamma, rules) = parse(String::from(file_path));

        let append = gamma.get("append").unwrap();
        let Rewrite(lhs, rhs) = rules[3].clone();

        let lhs_ty = type_check(lhs);
        let rhs_ty = type_check(rhs);
        println!("{:#?}", rhs_ty);
    }
}
