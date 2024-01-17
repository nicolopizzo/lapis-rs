#![allow(unused_variables)]
use core::panic;
use std::{
    alloc::System,
    borrow::BorrowMut,
    collections::HashMap,
    fmt::format,
    fs::{File, OpenOptions},
    hash::Hash,
    rc::{self, Rc},
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use indicatif::{ProgressBar, ProgressStyle};
use lazy_static::__Deref;
use log::{error, info, warn};

use crate::{
    debug,
    lgraph::LGraph,
    lnode::{snf, weak_head, LNode, NormalForms},
    parser::{Context, Rewrite, RewriteMap},
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
    let to_check = rules.iter().flat_map(|(_, x)| x).collect::<Vec<_>>();

    let bar = ProgressBar::new(to_check.len() as u64);
    let sty =
        ProgressStyle::with_template("[ {elapsed_precise} ] {bar:40} {pos:>7}/{len:<7} {msg}")
            .unwrap()
            .progress_chars("==-");
    bar.set_style(sty);
    bar.set_message("Checking rules");

    for Rewrite(lhs, rhs) in &to_check {
        bar.inc(1);

        // For debug purposes.
        // File::create("../../log/output.log").unwrap();

        let check = check_rule(lhs, rhs, rules);
        if let Err(e) = check {
            println!("Couldn't check {:?}", lhs);
            // return Err(e);
        }
    }

    bar.finish_with_message("Check completed.");

    Ok(())
}

fn check_rule(lhs: &Rc<LNode>, rhs: &Rc<LNode>, rules: &RewriteMap) -> Result<()> {
    info!("Inferring type for {:?}", lhs);
    let lhs_typ = debug!(type_infer(lhs, rules))?;
    if let Some(lhs_typ) = lhs_typ {
        info!("Inferred type: {:?}", lhs_typ);
        type_check(rhs, &lhs_typ, rules)?;
    } else {
        lhs.unsub_meta();
        let rhs_typ = type_infer(rhs, rules)?;
        if let Some(rhs_typ) = rhs_typ {
            type_check(lhs, &rhs_typ, rules)?;
        } else {
            return Err(Error::UnificationNeeded);
        }
    }

    lhs.unsub_meta();
    rhs.unsub_meta();

    Ok(())
}

fn type_infer(node: &Rc<LNode>, rules: &RewriteMap) -> Result<Option<Rc<LNode>>> {
    match &**node {
        LNode::App { left, right, .. } => {
            let left_ty = type_infer(left, rules)?;
            if left_ty.is_none() {
                return Ok(None);
            }

            let left_ty_whd = left_ty.unwrap();

            let left_ty_whd = weak_head(&left_ty_whd, rules);
            // Copio ricorsivamente il grafo, ma sharare le sostituzioni esplicite già esistenti
            // Posso anche sharare le parti dell'albero che non contengono `BVar`.
            let left_ty_whd = deep_clone(&mut HashMap::new(), &left_ty_whd);

            if let LNode::Prod { bvar, body, .. } = &*left_ty_whd {
                // check equality between left and `right_ty`
                let bvar_ty = bvar.get_type().expect("BVar must be typed in Product");
                type_check(right, &bvar_ty, rules)?;

                // substitute occurrences of `bvar` in `body` with `right`
                bvar.subs_to(right);

                let body = weak_head(body, rules);
                Ok(Some(body))
            } else {
                println!("{:?}", left_ty_whd);
                Err(Error::ProductExpected)
            }
        }
        LNode::Abs { bvar, body, .. } => {
            // let bvar_ty = type_infer(bvar, rules)?;
            let bvar_ty = bvar.get_type();
            if bvar_ty.is_none() {
                return Ok(None);
            }
            let bvar_ty = bvar_ty.unwrap();
            check_typeof(&bvar_ty, |node| node.is_type(), rules)?;

            // Porzione di codice nuova
            let xnew = LNode::new_bvar(Some(bvar_ty.clone()), Some("x'"));
            bvar.subs_to(&xnew);

            let body_ty = type_infer(body, rules)?;
            if body_ty.is_none() {
                return Ok(None);
            }

            let body_ty = body_ty.unwrap();
            check_typeof(&body_ty.clone(), |node| node.is_sort(), rules)?;

            bvar.unsub();
            let prod = LNode::new_prod(xnew, body_ty);
            Ok(Some(prod))
        }
        LNode::BVar { ty, .. } | LNode::Var { ty, .. } => Ok(ty.borrow().clone()),
        LNode::Prod { bvar, body, .. } => {
            let bvar_ty = bvar.get_type().expect("Variable is not typed.");
            check_typeof(&bvar_ty, |node| node.is_type(), rules)?;

            let body_ty = type_infer(body, rules)?;
            if body_ty.is_none() {
                return Ok(None);
            }

            let body_ty = body_ty.unwrap();
            check_typeof(&body_ty.clone(), |node| node.is_sort(), rules)?;

            Ok(Some(body_ty))
        }
        LNode::Type => Ok(Some(Rc::new(LNode::Kind))),
        LNode::Kind => Err(Error::TriedTypingKindSort),
    }
}

/// Verifies that inferring the type of `node` reduces to `typ_exp`.
fn type_check(term: &Rc<LNode>, typ_exp: &Rc<LNode>, rules: &RewriteMap) -> Result<()> {
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
                let pbvar_typ_exp = pbvar.get_type().expect("BVar in prod must be typed");

                if let Some(typ) = bvar_ty {
                    // if `typ` is not convertible to `typ_exp`, fail.
                    if !equality_check(&typ, &pbvar_typ_exp, rules) {
                        // println!("{:?} != {:?}", snf_typ, snf_typ_exp);
                        return Err(Error::TermsNotEquivalent);
                    };
                } else {
                    lbvar.infer_as(pbvar_typ_exp);
                }

                pbvar.bind_to_context();
                lbvar.subs_to(pbvar);

                type_check(lbody, pbody, rules)?;

                lbvar.unsub();
                pbvar.bind_to(typ_exp.clone());
            } else {
                return Err(Error::ProductExpected);
            }
        }
        LNode::Var { ty, .. } if ty.borrow().is_none() => {
            *ty.borrow_mut() = Some(typ_exp.clone());
        }
        LNode::BVar { ty, is_meta, .. } if ty.borrow().is_none() => {
            *ty.borrow_mut() = Some(typ_exp.clone());
        }
        _ => {
            let typ_inf = type_infer(term, rules)?;
            if typ_inf.is_none() {
                return Err(Error::UnificationNeeded);
            }

            let typ_inf = typ_inf.unwrap();

            // If `typ_inf` is not convertible to `typ_exp`, fail.
            if !equality_check(&typ_inf, &typ_exp, rules) {
                // info!("{:?} =/= {:?}", snf_typ_inf, snf_typ_exp);
                return Err(Error::TermsNotEquivalent);
            }
        }
    }

    Ok(())
}

fn timing<F, T>(fun: F) -> (T, u128)
where
    F: Fn() -> T,
{
    let start = SystemTime::now();
    let result = fun();
    let end = SystemTime::now();

    let time = end.duration_since(start).unwrap().as_millis();
    (result, time)
}

fn equality_check(r1: &Rc<LNode>, r2: &Rc<LNode>, rules: &RewriteMap) -> bool {
    let (r1_snf, t1) = timing(|| snf(r1, rules));
    let (r2_snf, t2) = timing(|| snf(r2, rules));

    let g = LGraph::from_roots(&r1_snf, &r2_snf);

    let subs = &mut HashMap::new();
    let r1_snf = deep_clone(subs, &r1_snf);
    let r2_snf = deep_clone(subs, &r2_snf);

    let (check_res, time) = timing(|| g.blind_check().is_ok() && g.var_check());

    check_res
}

fn check_typeof<F>(node: &Rc<LNode>, pred: F, rules: &RewriteMap) -> Result<()>
where
    F: Fn(Rc<LNode>) -> bool,
{
    let term = type_infer(node, rules)?;
    if term.is_none() {
        return Err(Error::GenericError);
    }

    let term = term.unwrap();
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
        assert!(check.is_ok(), "{:?}", check.unwrap_err());
    }

    #[test]
    fn testing() {
        before_each();
        env::set_current_dir("matita-light").expect("ERROR");
        let filepath = "matita_basics_logic.dk";

        let ctx = parse(filepath);

        // let tname = "matita_basics_logic.eq_ind_r";
        let tname = "matita_basics_logic.eqProp";
        // let tname = "matita_basics_logic.And_inv_ind";
        // let tname = "matita_basics_logic.Not_inv_rect_CProp2";
        // let tname = "matita_basics_logic.True_discr";

        let term = ctx.0.get(tname).unwrap();
        let size = term.size();
        let term = Rc::into_raw(term.clone()) as usize;

        let key = (term, size);
        let Rewrite(lhs, rhs) = ctx.1.get(&key).unwrap().first().unwrap();

        let check = check_rule(lhs, rhs, &ctx.1);
        // println!("{:?} --> {:?}", lhs, rhs);
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
