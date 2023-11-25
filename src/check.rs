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
use lazy_static::__Deref;
use log::{error, info, warn};

use crate::{
    debug,
    lgraph::LGraph,
    lnode::{snf, weak_head, LNode, NormalForms},
    parser::{Context, Rewrite},
    utils::{deep_clone, get_head},
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

pub fn check_context(ctx: &Context) -> Result<()> {
    let Context(gamma, rules) = ctx;
    // TODO: check definitions in gamma.

    for (_, term) in gamma {
        type_infer(term, rules)?;
    }

    let to_check = rules.iter().map(|(_, x)| x).flatten().collect::<Vec<_>>();

    let bar = ProgressBar::new(1);
    let sty = ProgressStyle::with_template("[ {elapsed_precise} ] {bar:40} Rule[{pos}] {msg}")
        .unwrap()
        .progress_chars("==-");
    bar.set_style(sty);
    bar.set_message("Checking rules");

    for (_, ruleset) in rules {
        bar.inc_length(ruleset.len() as u64);
        for Rewrite(lhs, rhs) in &to_check {
            bar.inc(1);

            // check_rule(lhs, rhs, &rules)?;

            // println!("{:?} --> {:?}", lhs, rhs);
            let check = check_rule(lhs, rhs, &rules);
            if let Err(e) = check {
                if e == Error::ProductExpected {
                    bar.finish();
                    println!("Something wrong.");
                    return Err(e);
                }
            }
        }
    }

    bar.finish_with_message("Check completed.");

    Ok(())
}

fn check_rule(
    lhs: &Rc<LNode>,
    rhs: &Rc<LNode>,
    rules: &HashMap<usize, Vec<Rewrite>>,
) -> Result<()> {
    let lhs_typ = type_infer(lhs, rules)?;
    if let Some(lhs_typ) = lhs_typ {
        println!("Checking...");
        type_check(rhs, &lhs_typ, rules)?;
        println!("Checked");
    } else {
        let rhs_typ = type_infer(rhs, rules)?;
        if let Some(rhs_typ) = rhs_typ {
            type_check(lhs, &rhs_typ, rules)?;
        } else {
            return Err(Error::UnificationNeeded);
        }
    }

    Ok(())
}

fn type_infer(node: &Rc<LNode>, rules: &HashMap<usize, Vec<Rewrite>>) -> Result<Option<Rc<LNode>>> {
    match &**node {
        LNode::App { left, right, .. } => {
            let left_ty = type_infer(&left, rules)?;
            if left_ty.is_none() {
                return Ok(None);
            }

            let left_whd = left_ty.unwrap();

            let left_whd = weak_head(&left_whd, rules);
            // Copio ricorsivamente il grafo, ma sharare le sostituzioni esplicite già esistenti
            // Posso anche sharare le parti dell'albero che non contengono `BVar`.
            let left_whd = deep_clone(&mut HashMap::new(), &left_whd);

            if let LNode::Prod { bvar, body, .. } = &*left_whd {
                assert!(bvar.is_bvar(), "`left` node in `Prod` is not a `BVar`.");

                // check equality between left and `right_ty`
                let bvar_ty = bvar.get_type().expect("BVar must be typed in Product");
                type_check(right, &bvar_ty, rules)?;

                // substitute occurrences of `bvar` in `body` with `right`
                if bvar.get_sub().is_none() {
                    bvar.subs_to(&right);
                }

                let body = weak_head(body, rules);
                return Ok(Some(body.clone()));
            } else {
                return Err(Error::ProductExpected);
            }
        }
        LNode::Abs { bvar, body, .. } => {
            let bvar_ty = bvar.get_type();
            if bvar_ty.is_none() {
                return Ok(None);
            }
            let bvar_ty = bvar_ty.unwrap();
            check_wkhd(&bvar_ty, |node| node.is_type(), rules)?;

            let body_ty = type_infer(body, rules)?;
            if body_ty.is_none() {
                return Ok(None);
            }

            let body_ty = body_ty.unwrap();
            check_wkhd(&body_ty.clone(), |node| node.is_sort(), rules)?;

            let prod = LNode::new_prod_unbound(bvar.clone(), body_ty.clone());
            let prod = deep_clone(&mut HashMap::new(), &prod);
            Ok(Some(prod))
        }
        LNode::BVar { .. } => Ok(node.get_type()),
        LNode::Var { .. } => Ok(node.get_type()),
        LNode::Prod { bvar, body, .. } => {
            let bvar_ty = bvar.get_type().expect("Variable is not typed.");
            check_wkhd(&bvar_ty, |node| node.is_type(), rules)?;

            let body_ty = type_infer(body, rules)?;
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

/// Verifies that inferring the type of `node` reduces to `typ_exp`.
fn type_check(
    term: &Rc<LNode>,
    typ_exp: &Rc<LNode>,
    rules: &HashMap<usize, Vec<Rewrite>>,
) -> Result<()> {
    match &**term {
        LNode::Abs {
            bvar: lbvar,
            body: lbody,
            ..
        } => {
            let typ_exp = weak_head(&typ_exp, rules);
            if let LNode::Prod {
                bvar: pbvar,
                body: pbody,
                ..
            } = &*typ_exp
            {
                let bvar_ty = lbvar.get_type();
                let typ_exp = pbvar.get_type().expect("BVar in prod must be typed");
                if let Some(typ) = bvar_ty {
                    // if `typ` is not convertible to `typ_exp`, fail.
                    let typ_exp = snf(&typ_exp, rules);
                    let typ = snf(&typ, rules);

                    if !equality_check(&typ, &typ_exp) {
                        println!("{:?} != {:?}", typ, typ_exp);
                        return Err(Error::TermsNotEquivalent);
                    }
                } else {
                    lbvar.infer_as(typ_exp);
                }

                type_check(&lbody, &pbody, rules)?
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
            println!("Inferring...");
            let typ_inf = type_infer(term, rules)?;
            println!("Inferred...");
            if typ_inf.is_none() {
                return Err(Error::UnificationNeeded);
            }

            let typ_inf = typ_inf.unwrap();

            // If `typ_inf` is not convertible to `typ_exp`, fail.
            let typ_inf = snf(&typ_inf, rules);
            let typ_exp = snf(&typ_exp, rules);

            if !equality_check(&typ_inf, &typ_exp) {
                println!("{:?} =/= {:?}", typ_inf, typ_exp);
                return Err(Error::TermsNotEquivalent);
            }
        }
    }

    Ok(())
}

fn equality_check(r1: &Rc<LNode>, r2: &Rc<LNode>) -> bool {
    // return true;
    let g = LGraph::from_roots(r1, r2);
    let check_res = g.blind_check();

    // g.blind_check().is_ok() && g.var_check()
    if let Err(e) = check_res {
        return false;
    } else {
        g.var_check()
        // true
    }
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
        // log4rs::init_file("log4rs.yaml", Default::default()).unwrap();

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
        let filepath = "dk_builtins.dk";

        let ctx = parse(filepath);

        let check = check_context(&ctx);
        assert!(check.is_ok(), "{:?}", check.unwrap_err());
    }

    #[test]
    fn test_matita() {
        before_each();
        env::set_current_dir("matita-light").expect("ERROR");
        // let filepath = "cic.dk";
        let filepath = "matita_basics_logic.dk";
        // let filepath = "matita_basics_types.dk";

        let ctx = parse(filepath);

        let check = check_context(&ctx);
        // assert!(check.is_ok(), "{:?}", check.unwrap_err());
    }

    #[test]
    fn testing() {
        before_each();
        env::set_current_dir("matita-light").expect("ERROR");
        let filepath = "matita_basics_logic.dk";

        let ctx = parse(filepath);

        // Problema con varcheck.
        let tname = "matita_basics_logic.eq_rect_r";

        // Problema con cic.prop != cic.type (cic.s (cic.s cic.z) )
        // let tname = "matita_basics_logic.True_discr";

        let term = ctx.0.get(tname).unwrap();
        let term = Rc::into_raw(term.clone()) as usize;
        let Rewrite(lhs, rhs) = ctx.1.get(&term).unwrap().first().unwrap();

        let check = check_rule(lhs, rhs, &ctx.1);
        assert!(check.is_ok(), "{:?}", check.unwrap_err());
    }

    #[test]
    fn test_prod_abs() {
        before_each();
        let filepath = "nat.dk";
        let c = parse(filepath);

        let check = check_context(&c);

        assert!(check.is_ok(), "{:?}", check.unwrap_err());
    }
}
