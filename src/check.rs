#![allow(unused_variables)]
use std::{collections::HashMap, rc::Rc};

use crate::{lgraph::LGraph, lnode::LNode, parser::Context};

fn type_check(node: Rc<LNode>) -> Option<Rc<LNode>> {
    match node.as_ref() {
        LNode::App { left, right, .. } => {
            let left_ty = type_check(left.clone()).unwrap();
            let right_ty = type_check(right.clone());
            
            // let left_whd = weak_head(left_ty); 
            
            assert!(
                left_ty.is_prod(),
                "Left node in application has not `Prod` type."
            );
            
            // Copio ricorsivamente il grafo, ma sharare le sostituzioni esplicite già esistenti
            // Posso anche sharare le parti dell'albero che non contengono `BVar`.

            if let LNode::Prod { bvar, body, .. } = left_ty.as_ref() {
                assert!(bvar.is_bvar(), "Left node in `Prod` is not a `BVar`.");

                // check equality between left and `right_ty`
                // TODO: uncomment for equality check
                if let Some(right_ty) = right_ty {
                    let bvar_ty = bvar.get_type().unwrap();

                    let g = LGraph::from_roots(bvar_ty, right_ty);

                    let res = g.blind_check();
                    assert!(res.clone().is_ok(), "{}", res.err().unwrap());
                    assert!(g.var_check());
                }

                // TODO: if `right_ty` is `None`, infer the type, so no need to check for equality (?)

                // substitute occurrences of `ll` in `lr` with `right`
                bvar.subs_to(right.clone());

                // TODO: c'è bisogno di fare un `unsub` di `left` in modo che la variabile bound non abbia più alcuna sostituzione
                // nel momento in cui si finisce di typecheckare `right`? Credo sia indifferente, ma semanticamente mi sembra corretto
                // effettuare un `unsub`.

                // let body_ty = type_check(body.clone());
                // left.unsub();
                // return lr_ty;

                return type_check(body.clone());
            }

            None
        }
        LNode::Abs { .. } => todo!(),
        LNode::BVar { ty, .. } => ty.clone(),
        LNode::Var { ty, .. } => ty.clone(),
        LNode::Prod { .. } => Some(node),
    }
}

mod tests {
    use crate::parser::{parse, Rewrite, print_context};

    use super::*;
    use std::{fmt::format, fs};

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
            let lhs_ty = type_check(lhs).unwrap();
            let rhs_ty = type_check(rhs).unwrap();
            println!("Rule#{}", idx);
            println!("lhs: {:p}, rhs: {:p}\n", lhs_ty, rhs_ty)
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
        let Rewrite(l, _) = rules[2].clone();

        // FIXME: type check with dependant types doesn't work
        let ty = type_check(l);
        println!("{:?}", ty)
    }
}
