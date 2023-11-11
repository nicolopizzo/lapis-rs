#![allow(unused_variables)]
use core::panic;
use std::{
    borrow::BorrowMut,
    collections::HashMap,
    fmt::format,
    hash::Hash,
    rc::{self, Rc},
};

use log::{error, info, warn};

use crate::{
    debug,
    lgraph::LGraph,
    lnode::{LNode, NormalForms},
    parser::{get_head, Context, Rewrite},
};

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    ProductExpected,
    AbstractionExpected,
    TriedTypingKindSort,
    TermsNotEquivalent,
    GenericError,
    UnificationNeeded
}
type Result<T> = std::result::Result<T, Error>;
static mut OPEN_DEBUG: usize = 0;

fn deep_clone(subs: &mut HashMap<usize, Rc<LNode>>, node: Rc<LNode>) -> Rc<LNode> {
    let node_ptr = Rc::into_raw(node.clone()) as usize;

    // Se ho già incontrato questo nodo, restituisco quello che ha preso il suo posto.
    if let Some(x) = subs.get(&node_ptr) {
        x.clone()
    } else {
        let new_node = match &*node {
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

fn snf(term: Rc<LNode>, rules: &HashMap<usize, Vec<Rewrite>>) -> Rc<LNode> {
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
            let nfs = normal_forms.borrow().clone();
            if nfs.is_none() {
                let term_snf = snf(subs_to, rules);
                *normal_forms.borrow_mut() = Some(NormalForms(true, Some(term_snf.clone())));

                term_snf
            } else {
                let NormalForms(_, term_snf) = nfs.unwrap();
                term_snf.unwrap()
            }
        }
        _ => term,
    }
}

fn weak_head(node: Rc<LNode>, rules: &HashMap<usize, Vec<Rewrite>>) -> Rc<LNode> {
    info!("Computing whnf of {:?}", node);
    let wnf = match &*node {
        LNode::App { left, right, .. } => {
            // Recursively weaken the head of the application.
            info!("Computing whnf of left={:?}", left);
            let left = debug!(weak_head(left.clone(), rules));
            info!("Computed: left_whnf = {:?}", left);
            let left = deep_clone(&mut HashMap::new(), left);

            if let LNode::Abs { bvar, body, .. } = &*left {
                bvar.subs_to(right.clone());
                debug!(weak_head(body.clone(), rules))
            } else {
                // Sono già in normal form.
                info!("Computing whnf of right={:?}", right);
                let right = debug!(weak_head(right.clone(), rules));
                info!("Computed: right_whnf = {:?}", right);
                LNode::new_app(left, right)
                // node.clone()
            }
        }
        LNode::BVar { subs_to, .. } if subs_to.borrow().is_some() => {
            let subs = subs_to.borrow().clone().unwrap();
            debug!(weak_head(subs, rules))
        }
        _ => node.clone(),
    };
    info!("Computed: {:?}", wnf);

    let head = get_head(wnf.clone());
    let head_ptr = Rc::into_raw(head.clone()) as usize;

    // For each possible rewrite rule, check if `wnf` matches with `lhs`. If `wnf` cannot be
    // rewritten to anything, the for is skipped (`&Vec::new()`) and `wnf` is returned.
    let empty = Vec::new();
    let rew = rules.get(&head_ptr).unwrap_or(&empty);
    info!("There are {} rules for {:?}", rew.len(), head);
    for Rewrite(lhs, rhs) in rew {
        info!("Analyzing match with rule {:?}", lhs);
        let mut subs = HashMap::new();
        let lhs = deep_clone(&mut subs, lhs.clone());
        let rhs = deep_clone(&mut subs, rhs.clone());

        // Mi mantengo un campo booleano per le metavariabili
        if debug!(matches(wnf.clone(), lhs.clone(), rules)) {
            info!("Rule matched, rewriting {:?}", rhs);
            return debug!(weak_head(rhs, rules));
        }
    }

    wnf
}

/// Verifies that `term` matches `lhs` up to weakening.
/// `pattern` is the left hand side of a rewrite rule, so it can only be `{ App, Var, BVar, Abs }`.
/// `term` must be in whnf.
fn matches(term: Rc<LNode>, pattern: Rc<LNode>, rules: &HashMap<usize, Vec<Rewrite>>) -> bool {
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

            let b1 = matches(l1.clone(), l2.clone(), rules);
            let b2 = matches(r1.clone(), r2.clone(), rules);
            b1 && b2
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
        ) => matches(l1.clone(), l2.clone(), rules) && matches(b1.clone(), b2.clone(), rules),
        (
            LNode::Abs {
                bvar: l1, body: b1, ..
            },
            LNode::Abs {
                bvar: l2, body: b2, ..
            },
        ) => {
            let b_res =
                matches(l1.clone(), l2.clone(), rules) && matches(b1.clone(), b2.clone(), rules);

            // TODO: come dovrei gestire le astrazioni?

            b_res
        }
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
fn type_check(
    node: Rc<LNode>,
    typ_exp: Rc<LNode>,
    rules: &HashMap<usize, Vec<Rewrite>>,
) -> Result<()> {
    match &*node {
        LNode::Abs { bvar, body, .. } => {
            info!("Computing whnf of typ_exp = {:?}", typ_exp);
            let typ_exp = debug!(weak_head(typ_exp, rules));
            info!("Computed: whnf = {:?}", typ_exp);
            if let LNode::Prod {
                bvar: a,
                body: body_ty,
                ..
            } = &*typ_exp
            {
                let bvar_ty = bvar.get_type();
                if let Some(typ) = bvar_ty {
                    // TODO: if `typ` is not convertible to `typ_exp`, fail.
                } else {
                    bvar.infer_as(a.clone());
                }

                info!("Type checking {:?} with typ_exp = {:?}", body, body_ty);
                debug!(type_check(body.clone(), body_ty.clone(), rules)?)
            } else {
                return Err(Error::ProductExpected);
            }
        }
        LNode::Var { ty, .. } if ty.borrow().is_none() => {
            *ty.borrow_mut() = Some(typ_exp);
        }
        LNode::BVar { ty, .. } if ty.borrow().is_none() => {
            *ty.borrow_mut() = Some(typ_exp);
        }
        _ => {
            info!("Inferring type for {:?}", node);
            let typ_inf = debug!(type_infer(node, rules)?);
            if typ_inf.is_none() {
                return Err(Error::UnificationNeeded);
            }

            let typ_inf = typ_inf.unwrap();
            info!("Type inferred: {:?}", typ_inf);
            // TODO: if `typ_inf` is not convertible to `typ_exp`, fail.
            // Add here alpha equivalence between `typ_inf` and `typ_exp`.
            // let typ_inf = snf(typ_inf, rules);
            // let typ_exp = snf(typ_exp, rules);

            // if !equality_check(typ_inf.clone(), typ_exp.clone()) {
            // return Err(Error::TermsNotEquivalent);
            // }
        }
    }

    Ok(())
}

fn check_wkhd<F>(node: Rc<LNode>, pred: F, rules: &HashMap<usize, Vec<Rewrite>>) -> Result<()>
where
    F: Fn(Rc<LNode>) -> bool,
{
    let term = type_infer(node, rules)?;
    if term.is_none() {
        return Err(Error::GenericError);
    }

    let term = term.unwrap();
    let term = weak_head(term, rules);
    assert!(pred(term));

    Ok(())
}

fn check_rule(lhs: Rc<LNode>, rhs: Rc<LNode>, rules: &HashMap<usize, Vec<Rewrite>>) -> Result<()> {
    if lhs.is_var() {
        info!("Checking rule {:?}: {:?} := {:?}", lhs, lhs.get_type(), rhs);
    } else {
        info!("Checking rule {:?} --> {:?}", lhs, rhs);
    }

    info!("Trying to infer type for lhs");
    let lhs_typ = debug!(type_infer(lhs.clone(), rules)?);
    if let Some(lhs_typ) = lhs_typ {
        info!("Type for lhs inferred: {:?}", lhs_typ);
        info!("Checking rhs with type inferred from lhs.");
        debug!(type_check(rhs, lhs_typ, rules)?);
        info!("Type checking done.")
    } else {
        info!("Type for lhs could not be inferred.");
        info!("Trying to infer type for rhs.");
        let rhs_typ = debug!(type_infer(rhs.clone(), rules)?);
        if let Some(rhs_typ) = rhs_typ {
            info!("Type for rhs inferred: {:?}", rhs_typ);
            info!("Checking lhs with type inferred from rhs.");
            debug!(type_check(lhs, rhs_typ, rules)?);
            info!("Type checking done.")
        } else {
            info!("Type for rhs could not be inferred. Error");
            return Err(Error::GenericError);
        }
    }

    Ok(())
}

fn type_infer(node: Rc<LNode>, rules: &HashMap<usize, Vec<Rewrite>>) -> Result<Option<Rc<LNode>>> {
    match &*node {
        LNode::App { left, right, .. } => {
            info!("Trying to infer type for {:?}", left);
            let left_ty = debug!(type_infer(left.clone(), rules)?);
            if left_ty.is_none() {
                info!("Infer for {:?} failed for strange reason.", left);
                return Ok(None);
            }
            info!("Type inferred correctly");

            let left_ty = left_ty.unwrap();

            info!("Computing whnf for {:?}", left);
            let left_whd = debug!(weak_head(left_ty.clone(), rules));
            info!("Computed: whnf = {:?}", left_whd);
            // Copio ricorsivamente il grafo, ma sharare le sostituzioni esplicite già esistenti
            // Posso anche sharare le parti dell'albero che non contengono `BVar`.
            let left_whd = deep_clone(&mut HashMap::new(), left_whd.clone());

            if let LNode::Prod { bvar, body, .. } = &*left_whd {
                assert!(bvar.is_bvar(), "`left` node in `Prod` is not a `BVar`.");

                // check equality between left and `right_ty`
                let bvar_ty = bvar.get_type().expect("BVar must be typed in Product");
                info!("Trying to check type of {:?} with {:?}", right, bvar_ty);
                debug!(type_check(right.clone(), bvar_ty, rules)?);
                info!("Type checking done, now substituting.");

                // substitute occurrences of `bvar` in `body` with `right`
                bvar.subs_to(right.clone());
                return Ok(Some(body.clone()));
            } else {
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

            let body_ty = debug!(type_infer(body.clone(), rules)?);
            if body_ty.is_none() {
                return Ok(None);
            }

            let body_ty = body_ty.unwrap();
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

            let body_ty = debug!(type_infer(body.clone(), rules)?);
            if body_ty.is_none() {
                return Ok(None);
            }

            let body_ty = body_ty.unwrap();
            check_wkhd(body_ty.clone(), |node| node.is_sort(), rules)?;

            Ok(Some(body_ty))
        }
        LNode::Type => Ok(Some(Rc::new(LNode::Kind))),
        LNode::Kind => Err(Error::TriedTypingKindSort),
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        debug,
        parser::{parse, print_context, Rewrite},
    };

    use super::*;
    use log4rs::{
        append::file::FileAppender,
        config::{Appender, Root},
        encode::pattern::PatternEncoder,
        Config,
    };
    use std::{collections::HashSet, env, fmt::format, fs, rc::Rc};

    fn before_each() {
        log4rs::init_file("log4rs.yaml", Default::default()).unwrap();

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

        for Rewrite(lhs, rhs) in rules.iter().map(|(_, value)| value).flatten() {
            // println!("{:?} --> {:?}", lhs, rhs);
            assert!(debug!(check_rule(lhs.clone(), rhs.clone(), &rules).is_ok()));
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

        for Rewrite(lhs, rhs) in rules.iter().map(|(_, value)| value).flatten() {
            println!("{:?} --> {:?}", lhs, rhs);
            assert!(check_rule(lhs.clone(), rhs.clone(), &rules).is_ok());
        }

        after_each();
    }

    #[test]
    fn test_dependant() {
        before_each();
        let file_path = "vec.dk";
        let Context(gamma, rules) = parse(String::from(file_path), &mut HashMap::new());
        print_context(&gamma);

        let append = gamma.get("vec.append").unwrap().clone().unwrap();
        println!("{:?}: {:?}", append, append.get_type().unwrap());

        let mut idx = 1;
        for Rewrite(lhs, rhs) in rules.iter().map(|(_, value)| value).flatten() {
            println!("{:?} --> {:?}", lhs, rhs);
            let check = check_rule(lhs.clone(), rhs.clone(), &rules);
            assert!(check.is_ok(), "Error: {:?}", check.unwrap_err());
            idx += 1;
        }
    }

    #[test]
    fn weaken_test_0() {
        // rule plus z n --> n
        let z = LNode::new_var(None, "z");
        let plus = LNode::new_var(None, "plus");
        let n = LNode::new_bvar(None, Some("n"));

        let lhs = LNode::new_app(plus.clone(), z.clone());
        let lhs = LNode::new_app(lhs, n.clone());

        let rhs = n.clone();

        let rule = Rewrite(lhs, rhs);

        // weaken something of the preceding form
        let s = LNode::new_var(None, "S");
        let arg = LNode::new_bvar(None, Some("x"));

        // plus z (S m) should rewrite to S m.
        let s_m = LNode::new_app(s.clone(), arg.clone());
        let term = LNode::new_app(plus.clone(), z.clone());
        let term = LNode::new_app(term, s_m.clone());

        // let weakened = weak_head(term, &vec![rule]);
        // assert_eq!(s_m, weakened.get_sub().unwrap());
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
        let n = LNode::new_bvar(nat.clone(), Some("n"));
        let m = LNode::new_bvar(nat.clone(), Some("m"));
        let app = LNode::new_app(plus, n);
        let app = LNode::new_app(app, m);

        after_each();
    }

    #[test]
    fn test_lib() {
        before_each();
        env::set_current_dir("focalide").expect("ERROR");

        let mod_name = "additive_law";
        let file_path = format!("{}.dk", mod_name);
        let c = parse(String::from(file_path), &mut HashMap::new());
        let Context(gamma, rules) = c;

        let mut index = 0;
        let mut errors = 0;
        for Rewrite(lhs, rhs) in rules.iter().map(|(_, value)| value).flatten() {
            let name = get_name(&gamma, lhs.clone());
            // Test only the rules of the module
            // if name.is_none() || !name.clone().unwrap().starts_with(mod_name) {
                // continue;
            // }
            let check = debug!(check_rule(lhs.clone(), rhs.clone(), &rules));
            if let Err(e) = check {
                // if e == Error::ProductExpected {
                    // error!(target: "CONSOLE", "{{ \n Rule did not check: {:?} --> {:?}\n}}", lhs, rhs);
                // }
                error!(target: "CONSOLE", "Could not check rule: error {:?} encountered", e);
                unsafe {
                    for n in 0..OPEN_DEBUG {
                        info!("}}");
                    }

                    OPEN_DEBUG = 0;
                }
                errors += 1;
            }
            index += 1;
        }

        let passed = index - errors;
        println!("{} / {} rules passed", passed, index);

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
