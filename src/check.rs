#![allow(unused_variables)]
use core::panic;
use std::{
    collections::HashMap,
    fmt::format,
    rc::{self, Rc},
};

use crate::{lgraph::LGraph, lnode::LNode, parser::Context};

fn deep_clone(subs: &mut HashMap<usize, Rc<LNode>>, node: Rc<LNode>) -> Rc<LNode> {
    match node.as_ref() {
        LNode::App { left, right, .. } => {
            let left = deep_clone(subs, left.clone());
            let right = deep_clone(subs, right.clone());

            Rc::new(LNode::new_app(left, right))
        }
        LNode::Prod { bvar, body, .. } => {
            let bvar = deep_clone(subs, bvar.clone());
            let body = deep_clone(subs, body.clone());

            Rc::new(LNode::new_prod(bvar, body))
        }
        LNode::Abs { bvar, body, .. } => {
            let bvar = deep_clone(subs, bvar.clone());
            let body = deep_clone(subs, body.clone());

            Rc::new(LNode::new_app(bvar, body))
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
            let left_ty = left.get_type().expect("`left` has not a type.");
            assert!(left_ty.is_prod(), "`left` has not `Prod` type.");

            if let LNode::Prod { bvar, body, .. } = left_ty.as_ref().clone() {
                assert!(bvar.is_bvar(), "`left` node in `Prod` is not a `BVar`.");

                // check equality between left and `right_ty`
                // TODO: uncomment for sharing equality
                // let bvar_ty = bvar.get_type().expect("Bvar is untyped");
                // let right_ty = right.get_type().expect("Right must have a type.");
                // equality_check(bvar_ty.clone(), right_ty.clone());

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
}

fn type_check(gamma: &HashMap<String, Rc<LNode>>, node: Rc<LNode>) -> Rc<LNode> {
    match node.as_ref() {
        LNode::App { left, right, .. } => {
            let left_ty = type_check(gamma, left.clone());
            let right_ty = type_check(gamma, right.clone());

            let left_whd = weak_head(left_ty.clone());

            assert!(
                left_whd.is_prod(),
                "`left` is not a `Prod` node in reducing weak head normal form."
            );

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
        LNode::Abs { bvar, body, .. } => Rc::new(LNode::new_prod(bvar.clone(), body.clone())),
        LNode::BVar { ty, .. } => {
            // if `ty` is `None`, the node should be a sort. Return it to test it.
            if ty.is_none() {
                return node
            }
            let ty = ty.clone().expect("Variable not typed");

            let type_sort = gamma.get("Type").expect("`Type` sort not in context.");
            let kind_sort = gamma.get("Kind").expect("`Kind` sort not in context.");
            let sort_ty = type_check(gamma, ty.clone());

            assert!(sort_ty == *type_sort || sort_ty == *kind_sort, "Base type is not a sort");

            ty
        }
        LNode::Var { ty, .. } => {
            // if `ty` is `None`, the node should be a sort. Return it to test it.
            if ty.is_none() {
                return node
            }

            let ty = ty.clone().expect("Variable not typed");
            let type_sort = gamma.get("Type").expect("`Type` sort not in context.");
            let kind_sort = gamma.get("Kind").expect("`Kind` sort not in context.");
            let sort_ty = type_check(gamma, ty.clone());

            assert!(sort_ty == *type_sort || sort_ty == *kind_sort, "Base type is not a sort");

            ty
        }
        LNode::Prod { bvar, body, .. } => {
            assert!(
                bvar.is_bvar(),
                "`bvar` in `Prod` node is not a bounded variable."
            );

            let bvar_ty = bvar.get_type().expect("Bounded variable is untyped.");
            let type_sort = gamma.get("Type").expect("`Type` sort not in context.");

            // bvar_ty.get_type() must be Type
            let bvar_ty = type_check(gamma, bvar_ty.clone());
            assert_eq!(bvar_ty, *type_sort);

            // Return sort of body (Type or Kind)
            type_check(gamma, body.clone())
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
