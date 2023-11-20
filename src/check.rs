#![allow(unused_variables)]
use core::panic;
use std::{
    borrow::BorrowMut,
    collections::HashMap,
    fmt::format,
    hash::Hash,
    rc::{self, Rc},
};

use indicatif::{ProgressBar, ProgressStyle};
use log::{error, info, warn};

use crate::{
    debug,
    lgraph::LGraph,
    lnode::{LNode, NormalForms},
    parser::{Context, Rewrite},
    utils::get_head,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    ProductExpected,
    AbstractionExpected,
    TriedTypingKindSort,
    TermsNotEquivalent,
    GenericError,
    UnificationNeeded,
}
type Result<T> = std::result::Result<T, Error>;
static mut OPEN_DEBUG: usize = 0;

fn deep_clone(subs: &mut HashMap<usize, Rc<LNode>>, node: &Rc<LNode>) -> Rc<LNode> {
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
                if bvar_new == *bvar && bvar_new == *bvar {
                    return node.clone();
                }

                LNode::new_prod(bvar_new, body_new)
            }
            LNode::Abs { bvar, body, .. } => {
                let bvar_new = deep_clone(subs, bvar);
                let body_new = deep_clone(subs, body);
                if bvar_new == *bvar && bvar_new == *bvar {
                    return node.clone();
                }

                LNode::new_abs(bvar_new, body_new)
            }

            LNode::BVar {
                subs_to, ty, symb, ..
            } => {
                let sub = subs_to.borrow();
                if sub.is_some() {
                    // Se c'è una sostituzione esplicita effettuo sharing
                    node.clone()
                } else {
                    // Deep cloning the Type
                    let ty = ty.borrow().clone();
                    let ty = ty.map(|ty| deep_clone(subs, &ty));

                    // FIXME: refactor correctly.
                    let symb = symb.clone().unwrap_or("_".to_string());
                    LNode::new_bvar(ty, Some(&symb))
                    // let ty_cloned = deep_clone(subs, ty);
                    // Rc::new(&*node.clone())
                }
            }

            // Var, Type and Kind can be shared
            _ => node.clone(),
        };
        subs.insert(node_ptr, new_node.clone());

        new_node
    }
}

fn snf(term: &Rc<LNode>, rules: &HashMap<usize, Vec<Rewrite>>) -> Rc<LNode> {
    let term = weak_head(term, rules);
    match &*term {
        LNode::Prod { bvar, body, .. } => {
            let bvar = snf(bvar, rules);
            let body = snf(body, rules);
            LNode::new_prod(bvar, body)
        }
        LNode::Abs { bvar, body, .. } => {
            let bvar = snf(bvar, rules);
            let body = snf(body, rules);
            LNode::new_abs(bvar, body)
        }
        LNode::App { left, right, .. } => {
            let left = snf(left, rules);
            let right = snf(right, rules);
            LNode::new_app(left, right)
        }
        LNode::BVar {
            subs_to,
            normal_forms,
            ..
        } if subs_to.borrow().is_some() => {
            let subs_to = subs_to.borrow().clone().unwrap();
            // TODO: Verifico che ci sia una snf: nel caso in cui c'è la restituisco, altrimenti la
            // calcolo e la salvo.
            let NormalForms(wnf_computed, computed_snf) = normal_forms.borrow().clone();
            if let Some(snf) = computed_snf {
                snf
            } else {
                let snf_term = snf(&subs_to, rules);
                *normal_forms.borrow_mut() = NormalForms(wnf_computed, Some(snf_term.clone()));

                snf_term
            }
        }
        _ => term,
    }
}

fn weak_head(node: &Rc<LNode>, rules: &HashMap<usize, Vec<Rewrite>>) -> Rc<LNode> {
    let wnf = match &**node {
        LNode::App { left, right, .. } => {
            // Recursively weaken the head of the application.
            let left = debug!(weak_head(left, rules));
            let left = deep_clone(&mut HashMap::new(), &left);

            if let LNode::Abs { bvar, body, .. } = &*left {
                bvar.subs_to(&right);
                debug!(weak_head(body, rules))
            } else {
                // Sono già in normal form.
                let right = debug!(weak_head(right, rules));
                LNode::new_app(left, right)
                // node.clone()
            }
        }
        LNode::BVar {
            subs_to,
            normal_forms,
            ..
        } if subs_to.borrow().is_some() => {
            let NormalForms(wnf_computed, snf) = normal_forms.borrow().clone();
            if wnf_computed {
                subs_to.borrow().clone().unwrap()
            } else {
                let subs = subs_to.borrow().clone().unwrap();
                let wnf = debug!(weak_head(&subs, rules));
                *normal_forms.borrow_mut() = NormalForms(true, snf);
                *subs_to.borrow_mut() = Some(wnf.clone());
                wnf
            }
        }
        _ => node.clone(),
    };

    let head = get_head(&wnf);
    let head_ptr = Rc::into_raw(head.clone()) as usize;

    // For each possible rewrite rule, check if `wnf` matches with `lhs`. If `wnf` cannot be
    // rewritten to anything, the for is skipped (`&Vec::new()`) and `wnf` is returned.
    let rew = rules.get(&head_ptr);
    if let Some(rew) = rew {
        for Rewrite(lhs, rhs) in rew {
            let mut subs = HashMap::new();
            let lhs = deep_clone(&mut subs, &lhs);
            let rhs = deep_clone(&mut subs, &rhs);

            // Mi mantengo un campo booleano per le metavariabili
            if debug!(matches(&wnf, &lhs, rules)) {
                return debug!(weak_head(&rhs, rules));
            }
        }
    }

    wnf
}

/// Verifies that `term` matches `lhs` up to weakening.
/// `pattern` is the left hand side of a rewrite rule, so it can only be `{ App, Var, BVar, Abs }`.
/// `term` must be in whnf.
fn matches(term: &Rc<LNode>, pattern: &Rc<LNode>, rules: &HashMap<usize, Vec<Rewrite>>) -> bool {
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
            // Il match avviene a meno di weakening.
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
            let subs = subs_to.borrow().clone().unwrap();
            matches(&subs, pattern, rules)
        }
        (_, LNode::BVar { subs_to, .. }) if subs_to.borrow().is_some() => {
            let subs = subs_to.borrow().clone().unwrap();
            matches(term, &subs, rules)
        }
        (
            tterm,
            LNode::BVar {
                subs_to,
                is_meta,
                canonic,
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
                match tterm {
                    LNode::BVar {
                        binder: t_binder, ..
                    } => {
                        // println!("{:?} ??? {:?}", term, pattern);
                        // Problema: `term` può essere una meta-variabile.
                        // invariante: il binder deve essere stato reso uguale in precedenza.
                        let c1 = t_binder.borrow().upgrade();
                        if c1.is_none() {
                            // println!("{:?} ?= {:?}", term, pattern);

                            return false;
                        }
                        let c1 = c1.expect("BVar has not a binder").canonic().upgrade();
                        let c2 = t_binder
                            .borrow()
                            .upgrade()
                            .expect("BVar has not a binder")
                            .canonic()
                            .upgrade();

                        if c2.is_none() {
                            // Ci finisce
                            // println!("ERROR::UNIF????");
                        }

                        c1 == c2
                    }
                    _ => false,
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

fn equality_check(r1: &Rc<LNode>, r2: &Rc<LNode>) -> bool {
    let g = LGraph::from_roots(r1, r2);
    let check_res = g.blind_check();
    if check_res.is_err() {
        return false;
    } else {
        g.var_check()
    }
}

/// Verifies that inferring the type of `node` reduces to `typ_exp`.
fn type_check(
    term: &Rc<LNode>,
    typ_exp: &Rc<LNode>,
    rules: &HashMap<usize, Vec<Rewrite>>,
) -> Result<()> {
    match &**term {
        LNode::Abs { bvar, body, .. } => {
            let typ_exp = debug!(weak_head(&typ_exp, rules));
            if let LNode::Prod {
                bvar: a,
                body: body_ty,
                ..
            } = &*typ_exp
            {
                let bvar_ty = bvar.get_type();
                if let Some(typ) = bvar_ty {
                    // TODO: if `typ` is not convertible to `typ_exp`, fail.
                    let typ = snf(&typ, rules);
                    let typ_exp = snf(&typ_exp, rules);

                    if !equality_check(&typ, &typ_exp) {
                        // println!("{:?} =/= {:?}", typ, typ_exp);
                        return Err(Error::TermsNotEquivalent);
                    }
                } else {
                    bvar.infer_as(a.clone());
                }

                debug!(type_check(body, body_ty, rules)?)
            } else {
                return Err(Error::ProductExpected);
            }
        }
        LNode::Var { ty, .. } if ty.borrow().is_none() => {
            *ty.borrow_mut() = Some(typ_exp.clone());
        }
        LNode::BVar { ty, .. } if ty.borrow().is_none() => {
            *ty.borrow_mut() = Some(typ_exp.clone());
        }
        _ => {
            let typ_inf = debug!(type_infer(term, rules)?);
            if typ_inf.is_none() {
                return Err(Error::UnificationNeeded);
            }

            let typ_inf = typ_inf.unwrap();

            // If `typ_inf` is not convertible to `typ_exp`, fail.
            // println!("{:?} ?= {:?}", typ_inf, typ_exp);
            let typ_inf = snf(&typ_inf, rules);
            let typ_exp = snf(&typ_exp, rules);

            if !equality_check(&typ_inf, &typ_exp) {
                // println!("{:?} =/= {:?}", typ_inf, typ_exp);
                return Err(Error::TermsNotEquivalent);
            }
        }
    }

    Ok(())
}

fn check_wkhd<F>(node: &Rc<LNode>, pred: F, rules: &HashMap<usize, Vec<Rewrite>>) -> Result<()>
where
    F: Fn(Rc<LNode>) -> bool,
{
    let term = type_infer(node, rules)?;
    if term.is_none() {
        return Err(Error::GenericError);
    }

    let term = term.unwrap();
    let term = weak_head(&term, rules);
    assert!(pred(term));

    Ok(())
}

fn check_rule(
    lhs: &Rc<LNode>,
    rhs: &Rc<LNode>,
    rules: &HashMap<usize, Vec<Rewrite>>,
) -> Result<()> {
    let lhs_typ = debug!(type_infer(lhs, rules)?);
    if let Some(lhs_typ) = lhs_typ {
        debug!(type_check(rhs, &lhs_typ, rules)?);
    } else {
        let rhs_typ = debug!(type_infer(rhs, rules)?);
        if let Some(rhs_typ) = rhs_typ {
            debug!(type_check(lhs, &rhs_typ, rules)?);
        } else {
            return Err(Error::UnificationNeeded);
        }
    }

    Ok(())
}

pub fn check_context(ctx: &Context) -> Result<()> {
    let Context(gamma, rules) = ctx;
    // TODO: check definitions in gamma.

    let to_check = rules.iter().map(|(_, x)| x).flatten().collect::<Vec<_>>();

    let bar = ProgressBar::new(to_check.len() as u64);
    let sty =
        ProgressStyle::with_template("[ {elapsed_precise} ] {bar:40} {pos:>7}/{len:<7} {msg}")
            .unwrap()
            .progress_chars("==-");
    bar.set_style(sty);
    bar.set_message("Checking rules");
    bar.tick();

    let mut errors = 0;
    for Rewrite(lhs, rhs) in &to_check {
        bar.inc(1);
        let check = check_rule(lhs, rhs, &rules);
        if let Err(e) = check {
            errors += 1;

            println!("Error: {:?}", e);
        }
    }

    bar.finish_with_message("Check completed.");
    println!("{} / {} rules had errors.", errors, to_check.len());

    Ok(())
}

fn type_infer(node: &Rc<LNode>, rules: &HashMap<usize, Vec<Rewrite>>) -> Result<Option<Rc<LNode>>> {
    match &**node {
        LNode::App { left, right, .. } => {
            let left_ty = debug!(type_infer(left, rules)?);
            if left_ty.is_none() {
                return Ok(None);
            }

            let left_ty = left_ty.unwrap();

            let left_whd = debug!(weak_head(&left_ty.clone(), rules));
            // Copio ricorsivamente il grafo, ma sharare le sostituzioni esplicite già esistenti
            // Posso anche sharare le parti dell'albero che non contengono `BVar`.
            let left_whd = deep_clone(&mut HashMap::new(), &left_whd);

            if let LNode::Prod { bvar, body, .. } = &*left_whd {
                assert!(bvar.is_bvar(), "`left` node in `Prod` is not a `BVar`.");

                // check equality between left and `right_ty`
                let bvar_ty = bvar.get_type().expect("BVar must be typed in Product");
                debug!(type_check(right, &bvar_ty, rules)?);

                // substitute occurrences of `bvar` in `body` with `right`
                bvar.subs_to(&right);
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
            check_wkhd(&bvar_ty, |node| node.is_type(), rules)?;

            let body_ty = debug!(type_infer(body, rules)?);
            if body_ty.is_none() {
                return Ok(None);
            }

            let body_ty = body_ty.unwrap();
            check_wkhd(&body_ty.clone(), |node| node.is_sort(), rules)?;

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
            check_wkhd(&bvar_ty, |node| node.is_type(), rules)?;

            let body_ty = debug!(type_infer(body, rules)?);
            if body_ty.is_none() {
                return Ok(None);
            }

            let body_ty = body_ty.unwrap();
            check_wkhd(&body_ty.clone(), |node| node.is_sort(), rules)?;

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
        parser::{parse, Rewrite},
    };

    use super::*;
    use indicatif::{ProgressBar, ProgressDrawTarget, ProgressIterator, ProgressStyle};
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

    #[test]
    fn test_simple() {
        before_each();
        let filepath = "nat.dk";
        let c = parse(filepath);

        let check = check_context(&c);

        assert!(check.is_ok(), "{:?}", check.unwrap_err());
    }

    #[test]
    fn test_cic() {
        before_each();
        let filepath = "cic.dk";
        let c = parse(filepath);

        let check = check_context(&c);

        assert!(check.is_ok(), "{:?}", check.unwrap_err());
    }

    #[test]
    fn test_dependant() {
        before_each();
        let filepath = "vec.dk";
        let c = parse(filepath);

        let check = check_context(&c);

        assert!(check.is_ok(), "{:?}", check.unwrap_err());
    }

    #[test]
    fn test_lib() {
        before_each();
        env::set_current_dir("focalide").expect("ERROR");
        let filepath = "additive_law.dk";

        let ctx = parse(filepath);

        let check = check_context(&ctx);
        assert!(check.is_ok(), "{:?}", check.unwrap_err());
    }

    #[test]
    fn test_matita() {
        before_each();
        env::set_current_dir("matita-light").expect("ERROR");
        let filepath = "univs.dk";
        // let filepath = "matita_basics_logic.dk";

        let ctx = parse(filepath);

        let check = check_context(&ctx);
        assert!(check.is_ok(), "{:?}", check.unwrap_err());
    }
}
