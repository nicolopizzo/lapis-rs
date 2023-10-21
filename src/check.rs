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
    match node.as_ref() {
        LNode::App { left, right, .. } => {
            let left_new = deep_clone(subs, left.clone());
            let right_new = deep_clone(subs, right.clone());
            if left_new == *left && right_new == *right {
                return node.clone();
            }

            Rc::new(LNode::new_app(left_new, right_new))
        }
        LNode::Prod { bvar, body, .. } => {
            let bvar_new = deep_clone(subs, bvar.clone());
            let body_new = deep_clone(subs, body.clone());
            if bvar_new == *bvar && bvar_new == *bvar {
                return node.clone();
            }

            Rc::new(LNode::new_prod(bvar_new, body_new))
        }
        LNode::Abs { bvar, body, .. } => {
            let bvar_new = deep_clone(subs, bvar.clone());
            let body_new = deep_clone(subs, body.clone());
            if bvar_new == *bvar && bvar_new == *bvar {
                return node.clone();
            }

            Rc::new(LNode::new_abs(bvar_new, body_new))
        }

        LNode::BVar { subs_to, .. } => {
            let sub = subs_to.borrow();
            if sub.is_some() {
                // Se c'è una sostituzione esplicita effettuo sharing
                node.clone()
            } else {
                // TODO: comment properly why the pointer is needed
                let node_ptr = Rc::into_raw(node.clone()) as usize;

                // Se ho già incontrato questa bounded variable, restituisco la variabile che ha preso il suo posto.
                if let Some(x) = subs.get(&node_ptr) {
                    x.clone()
                } else {
                    let x = Rc::new(node.as_ref().clone());

                    // Inserisco la sostituzione nella mappa.
                    subs.insert(node_ptr, x.clone());

                    x
                }
            }
        }

        LNode::Var { .. } => node.clone(),
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

fn type_check(gamma: &HashMap<String, Rc<LNode>>, node: Rc<LNode>) -> Rc<LNode> {
    match node.as_ref() {
        LNode::App { left, right, .. } => {
            let left_ty = type_check(gamma, left.clone());
            let right_ty = type_check(gamma, right.clone());

            let left_whd = weak_head(left_ty.clone());

            // Copio ricorsivamente il grafo, ma sharare le sostituzioni esplicite già esistenti
            // Posso anche sharare le parti dell'albero che non contengono `BVar`.
            // let right_ty = deep_clone(right_ty.clone());
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
            let bvar_ty = type_check(gamma, bvar.clone());
            let body_ty = type_check(gamma, body.clone());

            let body_sort = type_check(gamma, body_ty.clone());

            let bvar_ty = weak_head(bvar_ty);
            let body_sort = weak_head(body_sort.clone());

            let type_sort = gamma.get("Type").expect("Type sort is not in context.");
            let kind_sort = gamma.get("Kind").expect("Kind sort is not in context.");

            assert_eq!(bvar_ty, *type_sort);
            assert!(body_sort == *type_sort || body_sort == *kind_sort);

            Rc::new(LNode::new_prod(bvar.clone(), body_ty.clone()))
        }
        LNode::BVar { ty, .. } => ty.clone().expect("Variable is not typed."),
        LNode::Var { ty, .. } => ty.clone().expect("Variable is not typed."),
        LNode::Prod { bvar, body, .. } => {
            assert!(
                bvar.is_bvar(),
                "`bvar` in `Prod` node is not a bounded variable."
            );

            let bvar_ty = bvar.get_type().expect("Bounded variable is untyped.");
            let type_sort = gamma.get("Type").expect("`Type` sort not in context.");
            let kind_sort = gamma.get("Kind").expect("`Kind` sort not in context.");

            let bvar_ty = type_check(gamma, bvar_ty.clone());
            let bvar_ty = weak_head(bvar_ty);
            assert_eq!(bvar_ty, *type_sort);

            // Return sort of body (Type or Kind)
            let t = type_check(gamma, body.clone());

            // TODO: Weak head?
            let t = weak_head(t.clone());

            // test if t is Type or Kind
            assert!(t == *type_sort || t == *kind_sort);

            t
        }
    }
}

mod tests {
    use crate::parser::{parse, print_context, Rewrite};

    use super::*;
    use std::{fmt::format, fs, rc::Rc};

    #[test]
    fn test_simple() {
        let file_path = "examples/nat.dk";
        let cmds = fs::read_to_string(file_path);
        assert!(cmds.is_ok(), "Error reading file");
        let cmds = cmds.unwrap();

        let c = parse(cmds.to_string());
        print_context(&c);
        let Context(gamma, rules) = c;

        for (idx, Rewrite(lhs, rhs)) in (1..).zip(rules.into_iter()) {
            let lhs_ty = type_check(&gamma, lhs);
            let rhs_ty = type_check(&gamma, rhs);
            println!("Rule#{}", idx);
            println!("lhs: {:p}, rhs: {:p}\n", lhs_ty, rhs_ty)
        }
    }

    #[test]
    fn test_all() {
        let file_path = "examples/cic.dk";
        let cmds = fs::read_to_string(file_path);
        assert!(cmds.is_ok(), "Error reading file");
        let cmds = cmds.unwrap();

        let c = parse(cmds.to_string());
        print_context(&c);
        let Context(gamma, _) = c;

        for (key, value) in &gamma {
            // `Kind` sort is always well formed.
            if key == "Kind" {
                continue;
            }
            let ty = type_check(&gamma, value.clone());
            println!("{key: >8} --> {ty:p}");
        }
    }

    #[test]
    fn test_context() {
        let file_path = "examples/nat.dk";
        let cmds = fs::read_to_string(file_path);
        assert!(cmds.is_ok(), "Error reading file");
        let cmds = cmds.unwrap();

        let c = parse(cmds.to_string());
        print_context(&c);
        let Context(gamma, _) = c;

        for (key, value) in &gamma {
            // `Kind` sort is always well formed.
            if key == "Kind" {
                continue;
            }
            let ty = type_check(&gamma, value.clone());
            println!("{key: >8} --> {ty:p}");
        }
    }

    #[test]
    fn test_dependant() {
        let file_path = "examples/vec.dk";
        let cmds = fs::read_to_string(file_path);
        assert!(cmds.is_ok(), "Error reading file");
        let cmds = cmds.unwrap();

        let Context(gamma, rules) = parse(cmds.to_string());
        let append = gamma.get("append").unwrap();
        let Rewrite(lhs, rhs) = rules[2].clone();

        let lhs_ty = type_check(&gamma, lhs);
        let rhs_ty = type_check(&gamma, rhs);
        println!("{:#?}", lhs_ty);
    }
}