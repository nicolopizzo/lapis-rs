use core::panic;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt::format,
    fs,
    num::ParseFloatError,
    rc::Rc,
    result,
    sync::Mutex,
};

use crate::{lnode::LNode, utils::get_head};
use dedukti_parse::{
    term::{App, AppH},
    Intro, Lazy, Rule, Strict, Symb,
};
use indicatif::{ProgressBar, ProgressIterator, ProgressStyle};
use lazy_static::{__Deref, lazy_static};
use log::info;

pub enum Error {
    FileNotFound,
    GenericError,
}

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone)]
pub struct Rewrite(pub Rc<LNode>, pub Rc<LNode>);

pub type GammaMap = HashMap<String, Rc<LNode>>;
pub type RewriteMap = HashMap<(usize, usize), Vec<Rewrite>>;

#[derive(Debug, Clone)]
pub struct Context(pub GammaMap, pub RewriteMap);

lazy_static! {
    static ref OPEN_FILES: Mutex<HashSet<String>> = Mutex::new(HashSet::new());
}

// Utility types for referencing dedukti_parse nodes.
type TermType = App<AppH<Symb<String>, String>>;
type Command = dedukti_parse::Command<String, String, TermType>;
type ParseResult = Result<Command>;

pub fn parse(filepath: &str) -> Context {
    let mut ctx = Context(HashMap::new(), HashMap::new());
    parse_file(filepath, &mut ctx);

    ctx
}

fn parse_file(filepath: &str, ctx: &mut Context) {
    let cmds = fs::read_to_string(filepath);
    let cmds = cmds.expect("Error reading file");
    let path = filepath
        .strip_suffix(".dk")
        .expect("You can only read .dk files.");

    // let parse: result::Result<Vec<_>, _> =
    // Strict::<_, Symb<String>, String>::new(&cmds).collect();
    let cmds: result::Result<Vec<_>, _> =
        Lazy::<_, Symb<String>, String>::new(cmds.lines()).collect();
    let cmds = cmds.unwrap();

    let bar = ProgressBar::new(cmds.len() as u64);
    let sty =
        ProgressStyle::with_template("[ {elapsed_precise} ] {bar:40} {pos:>7}/{len:<7} {msg}")
            .unwrap()
            .progress_chars("==-");
    bar.set_style(sty);
    bar.set_message("Parsing...");
    bar.tick();

    for cmd in cmds {
        bar.inc(1);
        parse_command(&cmd, path, ctx);
    }
    bar.finish_with_message("Parsing completed.");
}

fn parse_command(cmd: &Command, path: &str, ctx: &mut Context) {
    match cmd {
        Command::Intro(name, args, intro) => {
            let mut loc_vars = Vec::new();
            for (vname, term) in args {
                // Using new_scope fixes problems of terms dependent on terms,
                // for example [n: Nat, v: Vec n].
                let typ = new_scope(ctx, &loc_vars, |ctx| map_term(&term, ctx, path));
                let vname = path.to_string() + "." + vname;
                let term = LNode::new_bvar(Some(typ), Some(vname.as_str()));

                loc_vars.push((vname.to_owned(), term));
            }

            new_scope(ctx, &loc_vars, |ctx| {
                let (typ, rhs) = parse_intro(intro, ctx, path);

                // Save symbol in context.
                let name = path.to_string() + "." + &name;
                let term = LNode::new_var(typ, &name);

                // If intro is a definition with `rhs`, then add a new rewrite rule
                if let Some(rhs) = rhs {
                    let head = get_head(&term);
                    let head_ptr = Rc::into_raw(head.clone()) as usize;

                    // create abstraction if `args` are specified.
                    if !loc_vars.is_empty() {
                        let rhs = loc_vars.iter().rev().fold(rhs.clone(), |body, (_, bvar)| {
                            LNode::new_abs(bvar.clone(), body)
                        });


                        ctx.1.insert((head_ptr, 1), vec![Rewrite(term.clone(), rhs)]);
                    } else {
                        ctx.1.insert((head_ptr, 1), vec![Rewrite(term.clone(), rhs)]);
                    }
                }

                ctx.0.insert(name, term);
            });
        }
        Command::Rules(rules) => {
            // Parse rewrite rules.
            let rules: Vec<_> = rules
                .into_iter()
                .map(|rule| parse_rule(rule, ctx, path))
                .collect();

            // Extend already existing rules.
            rules.into_iter().for_each(|rule| {
                let Rewrite(lhs, _) = &rule;
                let size = lhs.size();
                let head = get_head(lhs);
                let head_ptr = Rc::into_raw(head.clone()) as usize;

                let key = (head_ptr, size);

                if let Some(rules) = ctx.1.get_mut(&key) {
                    rules.push(rule);
                } else {
                    ctx.1.insert(key, vec![rule]);
                }
            });
        }
    }
}

fn parse_intro(
    node: &Intro<TermType>,
    ctx: &mut Context,
    modpath: &str,
) -> (Option<Rc<LNode>>, Option<Rc<LNode>>) {
    match node {
        // Declaration of a variable: `Nat: Type`.
        Intro::Declaration(ty) => {
            let ty = map_term(ty, ctx, modpath);

            (Some(ty), None)
        }
        Intro::Definition(ty, rhs) => {
            // ty is the type of the definition. If it is omitted, type synthesis will be necessary
            // with bidirectional typechecking. This is the only case in which this function can
            // return None as first member of the pair.
            let ty = ty.clone().map(|ty| map_term(&ty, ctx, modpath));

            let rhs = rhs.clone().map(|rhs| map_term(&rhs, ctx, modpath));

            (ty, rhs)
        }
        Intro::Theorem(ty, tz) => {
            // TODO: check if Ty is equal to Tz
            let ty = map_term(ty, ctx, modpath);
            let tz = map_term(tz, ctx, modpath);

            // Not considering tz for now.
            (Some(ty), None)
        }
    }
}

fn parse_rule(rule: &Rule<String, TermType>, ctx: &mut Context, path: &str) -> Rewrite {
    let mut vars = Vec::new();
    for (vname, term) in &rule.ctx {
        // Using new_scope fixes problems of terms dependent on terms,
        // for example [n: Nat, v: Vec n].
        let typ = term
            .clone()
            .map(|term| new_scope(ctx, &vars, |ctx| map_term(&term, ctx, path)));
        let vname = path.to_string() + "." + vname;
        let term = LNode::new_meta_var(typ, Some(vname.as_str()));

        vars.push((vname.to_owned(), term));
    }

    new_scope(ctx, &vars, |ctx| {
        let lhs = map_term(&rule.lhs, ctx, path);
        let rhs = map_term(&rule.rhs, ctx, path);

        Rewrite(lhs, rhs)
    })
}

fn map_term(term: &TermType, ctx: &mut Context, modpath: &str) -> Rc<LNode> {
    let App { head, args } = term;
    let vars: Vec<(String, Rc<LNode>)>;

    let head = match head {
        AppH::Atom(Symb { path, name }) => {
            if name == "Type" {
                return Rc::new(LNode::Type);
            } else if name == "_" {
                return LNode::new_meta_var(None, None);
            }

            let pathname = path.join(".");
            if !path.is_empty() && OPEN_FILES.lock().unwrap().insert(pathname.clone()) {
                let filename = pathname.clone() + ".dk";

                parse_file(&filename, ctx)
            }

            let name = if path.is_empty() {
                modpath.to_string() + "." + name
            } else {
                pathname + "." + name
            };

            // println!("{:#?}", ctx.0);
            let term = ctx
                .0
                .get(&name)
                .unwrap_or_else(|| panic!("Symbol {:?} not in scope", name));

            term.clone()
        }
        AppH::Abst(name, typ, body) => {
            // typ is optional, so it may be None
            let typ = typ.clone().map(|typ| map_term(&typ, ctx, modpath));
            let name = modpath.to_string() + "." + name;
            let bvar = LNode::new_bvar(typ, Some(&name));

            vars = vec![(name.to_string(), bvar.clone())];
            // Parse body with bvar in scope
            let body = new_scope(ctx, &vars, |ctx| map_term(body, ctx, modpath));
            LNode::new_abs(bvar, body)
        }
        AppH::Prod(name, typ, body) => {
            // typ is optional, so it may be None
            let typ = Some(map_term(&typ, ctx, modpath));
            let name = name.as_deref();
            let name = name.map(|name| modpath.to_string() + "." + name);
            let bvar = LNode::new_bvar(typ, name.as_deref());

            let body = if let Some(name) = name {
                vars = vec![((name.to_string(), bvar.clone()))];
                // Named product
                new_scope(ctx, &vars, |ctx| map_term(body, ctx, modpath))
            } else {
                // Simple product, `name` doesn't appear in body.
                map_term(body, ctx, modpath)
            };

            LNode::new_prod(bvar, body)
        }
    };

    // Apply args to head function.
    args.iter().fold(head.clone(), |acc, term| {
        let term = map_term(term, ctx, modpath);
        LNode::new_app(acc, term)
    })
}

fn new_scope<F, T>(ctx: &mut Context, vars: &Vec<(String, Rc<LNode>)>, mut inner_fun: F) -> T
where
    F: FnMut(&mut Context) -> T,
{
    let mut prev_symbols = HashMap::new();
    // Enter new scope.
    vars.iter().for_each(|(name, term)| {
        // consider previous symbols
        if let Some(term) = ctx.0.get(name) {
            prev_symbols.insert(name.to_string(), term.clone());
        }

        ctx.0.insert(name.to_string(), term.clone());
    });

    // Compute function result.
    let res = inner_fun(ctx);
    // Exit scope
    vars.iter().for_each(|(name, _)| {
        ctx.0.remove(name);
    });

    // Re-insert previous symbols.
    ctx.0.extend(prev_symbols);

    // Return function.
    res
}

mod tests {
    use log::info;
    use test_log::test;

    use super::*;
    use std::{env, fs, path::Path};

    fn setup() {
        env::set_current_dir("examples").expect("Could not set directory");
    }

    #[test]
    fn test_parse() {
        setup();
        env::set_current_dir("matita-light").expect("Could not set directory");
        let file_path = "matita_basics_logic.dk";
        let cmds = fs::read_to_string(file_path);
        assert!(cmds.is_ok(), "Error reading file");
        let cmds = cmds.unwrap();

        // DEBUG
        // let parse: ParseResult<_> = Strict::<_, Symb<&str>, &str>::new(&cmds).collect();
        let parse: Vec<_> = Strict::<_, Symb<String>, String>::new(&cmds).collect();
        // let parse = parse.unwrap();

        parse.iter().for_each(|x| println!("{:#?}", x))
    }

    #[test]
    fn test_simple() {
        setup();
        let file_path = "nat.dk";

        let c = parse(file_path);
        let Context(gamma, rules) = c;

        println!("{:#?}", gamma);
        rules
            .iter()
            .map(|(_, rule)| rule)
            .flatten()
            .for_each(|Rewrite(lhs, rhs)| println!("{:?} --> {:?}", lhs, rhs));
    }

    #[test]
    fn test_vec() {
        setup();
        let file_path = "vec.dk";

        let c = parse(file_path);
        let Context(gamma, rules) = c;

        println!("{:#?}", gamma);
        rules
            .iter()
            .map(|(_, rule)| rule)
            .flatten()
            .for_each(|Rewrite(lhs, rhs)| println!("{:?} --> {:?}", lhs, rhs));
    }

    #[test]
    fn test_focalide() {
        setup();
        env::set_current_dir("focalide").expect("Could not set directory");
        let file_path = "zen.dk";

        let _ = parse(file_path);
    }

    #[test]
    fn test_matita() {
        setup();
        env::set_current_dir("matita-light").expect("Could not set directory");
        let file_path = "matita_basics_logic.dk";

        let ctx = parse(file_path);

        let term = ctx.0.get("matita_basics_logic.eq_rect_r").unwrap();
        let head = get_head(term);
        let head_ptr = Rc::into_raw(head.clone()) as usize;

        // let rule = ctx.1.get(&head_ptr).unwrap();
        // println!("{:#?}", rule);
    }
}
