#![allow(unused_variables)]
use core::panic;
use std::{
    borrow::BorrowMut,
    collections::HashMap,
    fmt::format,
    hash::Hash,
    rc::{self, Rc},
};

use crate::{
    lgraph::LGraph,
    lnode::{LNode, NormalForms},
    parser::{Context, Rewrite},
};

#[derive(Debug, Clone)]
pub enum Error {
    ProductExpected,
    AbstractionExpected,
    TriedTypingKindSort,
    TermsNotEquivalent,
    GenericError,
}
type Result<T> = std::result::Result<T, Error>;

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

fn snf(term: Rc<LNode>, rules: &Vec<Rewrite>) -> Rc<LNode> {
    let term = weak_head(term, rules);
    match &*term {
        LNode::Prod { bvar, body, .. } => {
            let bvar = snf(bvar.clone(), rules);
            let body = snf(body.clone(), rules);
            LNode::new_prod(bvar, body)
        }
        LNode::Abs { bvar, body, .. } => {
            let bvar = snf(bvar.clone(), rules);
            let body = snf(body.clone(), rules);
            LNode::new_abs(bvar, body)
        }
        LNode::App { left, right, .. } => {
            let left = snf(left.clone(), rules);
            let right = snf(right.clone(), rules);
            LNode::new_app(left, right)
        }
        LNode::BVar {
            subs_to,
            normal_forms,
            ..
        } if subs_to.borrow().clone().is_some() => {
            let subs_to = subs_to.borrow().clone().unwrap();
            // TODO: Verifico che ci sia una snf: nel caso in cui c'è la restituisco, altrimenti la
            // calcolo e la salvo.
            let NormalForms(b, term_snf) = normal_forms.borrow().clone().expect("Error");
            if let Some(term_snf) = term_snf {
                term_snf
            } else {
                let term_snf = snf(subs_to, rules);
                *normal_forms.borrow_mut() = Some(NormalForms(b, Some(term_snf.clone())));

                term_snf
            }
        }
        _ => term,
    }
}

fn weak_head(node: Rc<LNode>, rules: &Vec<Rewrite>) -> Rc<LNode> {
    // Filtro le regole che si possono applicare in base alla variante della enumerazione. Se ho
    // una applicazione non c'è bisogno di controllare altro. Evito i numerosi match per il calcolo
    // della weak_head di qualcosa che non si può riscrivere in un altro modo.
    let poss_rules = rules
        .iter()
        .filter(|Rewrite(x, _)| core::mem::discriminant(&**x) == core::mem::discriminant(&*node));

    let wnf = match &*node {
        LNode::App { left, right, .. } => {
            // Recursively weaken the head of the application.
            let left = weak_head(left.clone(), rules);
            let left = deep_clone(&mut HashMap::new(), left);

            if let LNode::Abs { bvar, body, .. } = &*left {
                bvar.subs_to(right.clone());
                return weak_head(body.clone(), rules);
            } else {
                // Sono già in normal form.
                node.clone()
            }
        }
        _ => node.clone(),
    };

    for Rewrite(lhs, rhs) in poss_rules {
        let mut subs = HashMap::new();
        let lhs = deep_clone(&mut subs, lhs.clone());
        let rhs = deep_clone(&mut subs, rhs.clone());

        // Mi mantengo un campo booleano per le metavariabili
        if matches(wnf.clone(), lhs, rules) {
            return weak_head(rhs, rules);
        }
    }

    wnf
}

/// Verifies that `term` matches `lhs` up to weakening.
/// `pattern` is the left hand side of a rewrite rule, so it can only be `{ App, Var, BVar, Abs }`.
/// `term` must be in whnf.
fn matches(term: Rc<LNode>, pattern: Rc<LNode>, rules: &Vec<Rewrite>) -> bool {
    match (&*term, &*pattern) {
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
            // Il match avviene a meno di weakening.
            let l1 = weak_head(l1.clone(), rules);
            let r1 = weak_head(r1.clone(), rules);

            matches(l1.clone(), l2.clone(), rules) && matches(r1.clone(), r2.clone(), rules)
        }
        (LNode::BVar { subs_to, .. }, _) if subs_to.borrow().clone().is_some() => {
            let subs_to = subs_to.borrow().clone().unwrap();
            matches(subs_to, pattern, rules)
        }

        /*
         * 1. Devo distinguere metavariabili da variabili bound. Le variabili bound non si
         *    istanziano.
         * 2. Se è una metavar già istanziata => verifo l'alpha-eq tra termine e sostituito.
         * 3. Se è bound (variabile in lambda) deve essre bound dall'altra. Verifico con binder()
         *    il match dei binder. In questo caso non li istanzio. Faccio puntare un puntatore con
         *    .canonic() i binder.
         * */
        (_, LNode::BVar { ty, subs_to, .. }) => {
            // let typ_exp = ty.borrow().clone().expect("Missing typ_exp.");
            // type_check(term.clone(), typ_exp, rules);
            *subs_to.borrow_mut() = Some(term);

            true
        }
        // TODO: implementare astrazioni e prodotti
        (
            LNode::Prod {
                bvar: l1, body: b1, ..
            },
            LNode::Prod {
                bvar: l2, body: b2, ..
            },
        ) => todo!(),
        (
            LNode::Abs {
                bvar: l1, body: b1, ..
            },
            LNode::Abs {
                bvar: l2, body: b2, ..
            },
        ) => todo!(),
        // Constant variables, sorts.
        _ => term == pattern,
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
fn type_check(node: Rc<LNode>, typ_exp: Rc<LNode>, rules: &Vec<Rewrite>) {
    match &*node {
        LNode::Abs { bvar, body, .. } => {
            let bvar_ty = bvar.get_type();
            let typ_exp = weak_head(typ_exp, rules);
            if let LNode::Prod {
                bvar: a,
                body: body_ty,
                ..
            } = &*typ_exp
            {
                if let Some(typ) = bvar_ty {
                    // TODO: if `typ` is not convertible to `typ_exp`, fail.
                } else {
                    bvar.infer_as(a.clone());
                }

                type_check(body.clone(), body_ty.clone(), rules)
            } else {
                // return Err(Error::ProductExpected);
            }
        }
        LNode::Var { ty, .. } if ty.borrow().is_none() => {
            *ty.borrow_mut() = Some(typ_exp);
        }
        LNode::BVar { ty, .. } if ty.borrow().is_none() => {
            *ty.borrow_mut() = Some(typ_exp);
        }
        _ => {
            let typ_inf = type_infer(node, rules);
            if let Err(e) = typ_inf {
                panic!("{:?}", e);
            }

            let typ_inf = typ_inf.unwrap().expect("Type could not be inferred");
            // TODO: if `typ_inf` is not convertible to `typ_exp`, fail.
            // Add here alpha equivalence between `typ_inf` and `typ_exp`.
            let typ_inf = snf(typ_inf, rules);
            let typ_exp = snf(typ_exp, rules);

            if !equality_check(typ_inf.clone(), typ_exp.clone()) {
                dbg!(typ_inf);
                dbg!(typ_exp);
                panic!("Terms could not be compared.");
                // return Err(Error::TermsNotEquivalent);
            }
        }
    }
}

fn check_wkhd<F>(node: Rc<LNode>, pred: F, rules: &Vec<Rewrite>) -> Result<()>
where
    F: Fn(Rc<LNode>) -> bool,
{
    let node = type_infer(node, rules)?.unwrap();
    let node = weak_head(node, rules);
    assert!(pred(node));

    Ok(())
}

fn check_rule(lhs: Rc<LNode>, rhs: Rc<LNode>, rules: &Vec<Rewrite>) -> Result<()> {
    let lhs_typ = type_infer(lhs.clone(), rules)?;
    if let Some(lhs_typ) = lhs_typ {
        type_check(rhs, lhs_typ, rules);
    } else {
        let rhs_typ = type_infer(rhs.clone(), rules)?;
        if let Some(rhs_typ) = rhs_typ {
            type_check(lhs, rhs_typ, rules);
        } else {
            return Err(Error::GenericError);
            // println!(
            // "[ WARN ] Could need unification for {:?} --> {:?}",
            // lhs, rhs
            // );
        }
    }

    Ok(())
}

fn type_infer(node: Rc<LNode>, rules: &Vec<Rewrite>) -> Result<Option<Rc<LNode>>> {
    match node.as_ref() {
        LNode::App { left, right, .. } => {
            let left_ty = type_infer(left.clone(), rules)?;
            if left_ty.is_none() {
                return Ok(None);
            }

            let left_ty = left_ty.unwrap();

            let left_whd = weak_head(left_ty.clone(), rules);

            // Copio ricorsivamente il grafo, ma sharare le sostituzioni esplicite già esistenti
            // Posso anche sharare le parti dell'albero che non contengono `BVar`.
            let left_whd = deep_clone(&mut HashMap::new(), left_whd.clone());

            if let LNode::Prod { bvar, body, .. } = left_whd.as_ref() {
                assert!(bvar.is_bvar(), "`left` node in `Prod` is not a `BVar`.");

                // check equality between left and `right_ty`
                let bvar_ty = bvar.get_type().expect("BVar must be typed in Product");
                // type_check(right.clone(), bvar_ty, rules);

                // substitute occurrences of `bvar` in `body` with `right`
                bvar.subs_to(right.clone());
                return Ok(Some(body.clone()));
            } else {
                // FIXME: Parsing della grande libreria si blocca qui.
                return Err(Error::ProductExpected);
            }
        }
        LNode::Abs { bvar, body, .. } => {
            assert!(
                bvar.is_bvar(),
                "`bvar` in `Abs` node is not a bounded variable."
            );

            let bvar_ty = bvar.get_type();
            if bvar_ty.is_none() {
                return Ok(None);
            }
            let bvar_ty = bvar_ty.unwrap();
            check_wkhd(bvar_ty, |node| node.is_type(), rules)?;

            let body_ty = type_infer(body.clone(), rules)?.unwrap();
            check_wkhd(body_ty.clone(), |node| node.is_sort(), rules)?;

            Ok(Some(LNode::new_prod(bvar.clone(), body_ty.clone())))
        }
        LNode::BVar { .. } => Ok(node.get_type()),
        LNode::Var { .. } => Ok(node.get_type()),
        LNode::Prod { bvar, body, .. } => {
            assert!(
                bvar.is_bvar(),
                "`bvar` in `Prod` node is not a bounded variable."
            );

            let bvar_ty = bvar.get_type().expect("Variable is not typed.");
            check_wkhd(bvar_ty, |node| node.is_type(), rules)?;

            let body_ty = type_infer(body.clone(), rules)?.unwrap();
            check_wkhd(body_ty.clone(), |node| node.is_sort(), rules)?;

            Ok(Some(body_ty))
        }
        LNode::Type => Ok(Some(Rc::new(LNode::Kind))),
        LNode::Kind => Err(Error::TriedTypingKindSort),
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
        let c = parse(String::from(file_path), &mut HashMap::new());

        let Context(gamma, rules) = c;
        print_context(&gamma);

        for Rewrite(lhs, rhs) in rules.clone() {
            assert!(check_rule(lhs, rhs, &rules).is_ok());
        }

        after_each();
    }

    #[test]
    fn test_all() {
        before_each();
        let file_path = "cic.dk";
        let c = parse(String::from(file_path), &mut HashMap::new());
        let Context(gamma, rules) = c;
        print_context(&gamma);

        for Rewrite(lhs, rhs) in rules.clone() {
            assert!(check_rule(lhs, rhs, &rules).is_ok());
        }

        after_each();
    }

    #[test]
    fn test_dependant() {
        before_each();
        let file_path = "vec.dk";
        let Context(gamma, rules) = parse(String::from(file_path), &mut HashMap::new());
        print_context(&gamma);

        // let append = gamma.get("append").unwrap();

        let mut idx = 1;
        for Rewrite(lhs, rhs) in rules.clone() {
            println!("Trying to type rule#{idx:?}");
            let check = check_rule(lhs, rhs, &rules);
            assert!(check.is_ok(), "Error: {:?}", check.unwrap_err());
            idx += 1;
        }
    }

    #[test]
    fn weaken_test_0() {
        // rule plus z n --> n
        let z = LNode::new_var(None);
        let plus = LNode::new_var(None);
        let n = LNode::new_bvar(None);

        let lhs = LNode::new_app(plus.clone(), z.clone());
        let lhs = LNode::new_app(lhs, n.clone());

        let rhs = n.clone();

        let rule = Rewrite(lhs, rhs);

        // weaken something of the preceding form
        let s = LNode::new_var(None);
        let arg = LNode::new_bvar(None);

        // plus z (S m) should rewrite to S m.
        let s_m = LNode::new_app(s.clone(), arg.clone());
        let term = LNode::new_app(plus.clone(), z.clone());
        let term = LNode::new_app(term, s_m.clone());

        let weakened = weak_head(term, &vec![rule]);
        assert_eq!(s_m, weakened.get_sub().unwrap());
    }

    /// Test that `plus z (plus x y)` rewrites to `plus x y`.
    #[test]
    fn weaken_test_1() {
        // rule plus z n --> n
        let z = LNode::new_var(None);
        let plus = LNode::new_var(None);
        let n = LNode::new_bvar(None);

        let lhs = LNode::new_app(plus.clone(), z.clone());
        let lhs = LNode::new_app(lhs, n.clone());

        let rhs = n.clone();

        let rule = Rewrite(lhs, rhs);

        // custom input: plus z (plus x y).
        let x = LNode::new_bvar(None);
        let y = LNode::new_bvar(None);

        let p_xy = LNode::new_app(plus.clone(), x.clone());
        let p_xy = LNode::new_app(plus.clone(), y.clone());
        let term = LNode::new_app(plus.clone(), z.clone());
        let term = LNode::new_app(term, p_xy.clone());

        // Verify `plus z (plus x y) --> plus x y`
        let weakened = weak_head(term, &vec![rule]);
        assert_eq!(p_xy, weakened.get_sub().unwrap());
    }

    #[test]
    fn weaken_test_2() {
        before_each();

        let file_path = "nat.dk";
        let Context(gamma, rules) = parse(String::from(file_path), &mut HashMap::new());

        let plus = gamma.get("plus").unwrap().clone().unwrap();
        let s = gamma.get("S").unwrap().clone().unwrap();
        let z = gamma.get("zero").unwrap().clone().unwrap();

        let m = LNode::new_app(s, z);
        let n = LNode::new_bvar(None);
        let app = LNode::new_app(plus, m);
        let app = LNode::new_app(app, n);

        let weakened = weak_head(app, &rules);

        after_each();
    }

    #[test]
    fn test_snf_1() {
        before_each();

        let file_path = "vec.dk";
        let Context(gamma, rules) = parse(String::from(file_path), &mut HashMap::new());

        let append = gamma.get("vec.append").unwrap();
        let Rewrite(lhs, rhs) = rules[2].clone();
        print_context(&gamma);

        let lhs_inf = type_infer(lhs, &rules).unwrap().unwrap();
        let lhs_snf = snf(lhs_inf.clone(), &rules);
        let rhs_inf = type_infer(rhs, &rules);

        after_each();
    }

    #[test]
    fn test_snf_2() {
        before_each();

        let file_path = "nat.dk";
        let Context(gamma, rules) = parse(String::from(file_path), &mut HashMap::new());

        let plus = gamma.get("nat.plus").unwrap().clone().unwrap();
        let s = gamma.get("nat.S").unwrap().clone().unwrap();
        let z = gamma.get("nat.zero").unwrap().clone().unwrap();

        let one = gamma.get("nat.1").unwrap().clone().unwrap();
        let two = gamma.get("nat.2").unwrap().clone().unwrap();
        let three = gamma.get("nat.3").unwrap().clone().unwrap();

        let p_one_two = LNode::new_app(plus, one);
        let p_one_two = LNode::new_app(p_one_two, two);

        print_context(&gamma);
        let p_one_two = snf(p_one_two, &rules);
        let three = snf(three, &rules);
        assert!(equality_check(p_one_two, three));

        after_each();
    }

    #[test]
    fn test_snf_3() {
        before_each();
        let file_path = "vec.dk";
        let Context(gamma, rules) = parse(String::from(file_path), &mut HashMap::new());

        let plus = gamma.get("plus").unwrap().clone().unwrap();
        let nat = gamma.get("Nat").unwrap();
        print_context(&gamma);

        // snf(plus n m) should be plus n m.
        let n = LNode::new_bvar(nat.clone());
        let m = LNode::new_bvar(nat.clone());
        let app = LNode::new_app(plus, n);
        let app = LNode::new_app(app, m);

        after_each();
    }

    #[test]
    fn test_lib() {
        before_each();
        env::set_current_dir("focalide").expect("ERROR");

        let file_path = "additive_law.dk";
        let c = parse(String::from(file_path), &mut HashMap::new());
        let Context(gamma, rules) = c;
        print_context(&gamma);

        let mut index = 0;
        for Rewrite(lhs, rhs) in rules.clone() {
            println!("Checking rule#{}", index);
            // let rule_name = get_name(&gamma, lhs.clone()).unwrap();
            let check = check_rule(lhs, rhs, &rules);
            assert!(check.is_ok(), "{:?}", check.unwrap_err());
            index += 1;
        }

        let _ = env::set_current_dir("..");
        after_each();
    }
}

fn get_name(gamma: &HashMap<String, Option<Rc<LNode>>>, term: Rc<LNode>) -> Option<String> {
    match &*term {
        LNode::App { left, .. } => get_name(gamma, left.clone()),
        LNode::Var { .. } => {
            for (key, value) in gamma {
                if let Some(value) = value {
                    if value.clone() == term {
                        return Some(key.clone());
                    }
                }
            }

            None
            // gamma.into_iter().find(|(key, value)| **value == term).map(|(key, _)| key.clone())
        }
        _ => unreachable!(),
    }
}
