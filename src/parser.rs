use core::panic;
use std::{
    collections::{HashMap, HashSet},
    fs,
    rc::Rc,
    sync::Mutex,
};

use dedukti_parse::{
    term::{App, AppH},
    Command, Intro, Rule, Strict, Symb,
};
use lazy_static::lazy_static;

use crate::lnode::LNode;

type ParseResult<'a, T> = std::result::Result<Vec<T>, dedukti_parse::Error>;

#[derive(Debug, Clone)]
pub struct Rewrite(pub Rc<LNode>, pub Rc<LNode>);
#[derive(Debug, Clone)]
pub struct Context(pub HashMap<String, Option<Rc<LNode>>>, pub Vec<Rewrite>);

lazy_static! {
    static ref OPEN_FILES: Mutex<HashSet<String>> = Mutex::new(HashSet::new());
}

/// Utility function for ternary operator.
fn ife<T>(cond: bool, t: T, f: T) -> T {
    if cond {
        t
    } else {
        f
    }
}

fn parse_rule(
    gamma: &mut HashMap<String, Option<Rc<LNode>>>,
    rule: Rule<&str, App<AppH<Symb<&str>, &str>>>,
) -> Rewrite {
    // Clone gamma to have a local context.
    let mut gamma = gamma.clone();
    for v in rule.ctx {
        let (vname, ty) = v;
        let ty = ty.map(|ty| map_to_node(&mut gamma, ty).unwrap());
        let node = LNode::new_bvar(ty.clone());
        gamma.insert(vname.to_string(), Some(node));
    }

    let lhs = map_to_node(&mut gamma, rule.lhs).unwrap();
    let rhs = map_to_node(&mut gamma, rule.rhs).unwrap();

    Rewrite(lhs, rhs)
}

fn map_to_node(
    gamma: &mut HashMap<String, Option<Rc<LNode>>>,
    app: App<AppH<Symb<&str>, &str>>,
) -> Option<Rc<LNode>> {
    let head = match app.head.clone() {
        AppH::Atom(Symb { path, name }) => {
            // start new parsing if `path` has not been encountered.
            let path_string = path.join(".");
            if !path.is_empty() && !OPEN_FILES.lock().unwrap().contains(&path_string) {
                OPEN_FILES.lock().unwrap().insert(path_string.clone());
                let filepath = format!("{path_string}.dk");
                let Context(gamma_new, _) = parse(filepath);
                gamma.extend(gamma_new.into_iter().map(|(key, value)| {
                    let key = format!("{path_string}.{key}");
                    (key, value)
                }));
            }

            if name == "Type" {
                Some(Rc::new(LNode::Type))
            } else {
                let name = ife(
                    path.is_empty(),
                    name.to_string(),
                    format!("{path_string}.{}", name.to_string())
                );
                gamma
                    .get(&name)
                    .map(|t| t.clone())
                    .expect("Symbol {name:?} is not in context")
            }
        }
        AppH::Abst(x, t, body) => {
            let t = t.map(|t| {
                map_to_node(gamma, t.as_ref().clone()).expect("No type inference admitted.")
            });

            let node = LNode::new_bvar(t);
            gamma.insert(x.to_owned(), Some(node.clone()));
            let body = map_to_node(gamma, body.as_ref().clone()).unwrap();
            let abs = LNode::new_abs(node.clone(), body);

            Some(abs)
        }
        AppH::Prod(x, a, t) => {
            let a = map_to_node(gamma, a.as_ref().clone());

            match x {
                Some(x) => {
                    let mut gamma = gamma.clone();
                    // If product has name `x`, save it as a variable node with type `a`.
                    let a = LNode::new_bvar(a);
                    gamma.insert(x.to_string(), Some(a.clone()));
                    let t = map_to_node(&mut gamma, t.as_ref().clone()).unwrap();

                    let node = LNode::new_prod(a.clone(), t.clone());

                    Some(node)
                }
                None => {
                    let a = LNode::new_bvar(a);
                    let t = map_to_node(gamma, t.as_ref().clone()).unwrap();

                    let node = LNode::new_prod(a.clone(), t.clone());

                    Some(node)
                }
            }
        }
    };

    let mut res = head;
    // Apply all the arguments to the head node (left application)
    for arg in app.args {
        // if arg is a wildcard, apply a var on which you can infer
        let node = if let AppH::Atom(Symb { name: "_", .. }) = arg.head {
            LNode::new_var(None)
        } else {
            map_to_node(gamma, arg.clone()).expect("Something went wrong")
        };

        res = Some(LNode::new_app(res.unwrap(), node));
    }

    res
}

pub fn print_context(gamma: &HashMap<String, Option<Rc<LNode>>>) {
    println!("{}", "-".repeat(37));
    println!("| {0: <10} | {1: <20} |", "Symbol", "Address");
    println!("{}", "-".repeat(37));
    for (key, ty) in gamma {
        if let Some(ty) = ty {
            println!("| {0: <10} | {1: <20p} |", key, *ty);
        } else {
            println!("| {0: <10} | {1: <20} |", key, "None");
        }
    }
    println!("{}", "-".repeat(37));
}

pub fn parse(filepath: String) -> Context {
    let cmds = fs::read_to_string(&filepath);
    let cmds = cmds.expect("File not found.");

    let parse: ParseResult<_> = Strict::<_, Symb<&str>, &str>::new(&cmds).collect();
    let parse = parse.unwrap();

    let mut gamma = HashMap::new();
    let mut rew_rules = Vec::new();

    for cmd in parse {
        match cmd {
            Command::Intro(name, _, it) => {
                match it {
                    Intro::Declaration(x) => {
                        let t = map_to_node(&mut gamma, x);
                        let node = LNode::new_var(t);

                        gamma.insert(name.to_string(), Some(node));
                    }
                    Intro::Definition(x, y) => {
                        // if Some(x) = x => t = map_to_node(..), altrimenti è None (caso di
                        // inferenza da checkare con bidirectional type_check).
                        let ty = x.map(|x| map_to_node(&mut gamma, x).expect("Error encountered"));
                        let node = LNode::new_var(ty);
                        gamma.insert(name.to_string(), Some(node.clone()));

                        // if `def x := ...`, add y to rewrite rules.
                        if let Some(y) = y {
                            let mut gamma = gamma.clone();
                            let lhs = node;
                            let rhs = map_to_node(&mut gamma, y).unwrap();
                            rew_rules.push(Rewrite(lhs, rhs));
                        }
                    }
                    Intro::Theorem(_, _) => {
                        // TODO: parse thm
                        todo!()
                    }
                }
            }
            Command::Rules(rules) => {
                let mut rules = rules
                    .iter()
                    .map(|rule| parse_rule(&mut gamma, rule.clone()))
                    .collect();

                rew_rules.append(&mut rules);
            }
        }
    }

    Context(gamma, rew_rules)
}

mod tests {
    use super::*;
    use std::{env, fs, path::Path};

    fn setup() {
        env::set_current_dir("examples").expect("Could not set directory");
    }

    #[test]
    fn test_parse() {
        setup();
        let file_path = "nat.dk";
        let cmds = fs::read_to_string(file_path);
        assert!(cmds.is_ok(), "Error reading file");
        let cmds = cmds.unwrap();

        // DEBUG
        let parse: ParseResult<_> = Strict::<_, Symb<&str>, &str>::new(&cmds).collect();
        let parse = parse.unwrap();

        parse.iter().for_each(|x| println!("{:?}", x))
    }

    #[test]
    fn test_simple() {
        setup();
        let file_path = "nat.dk";

        let c = parse(file_path.to_string());
        let Context(gamma, _) = c;
        print_context(&gamma);

        let nat = gamma.get("Nat").unwrap().clone().unwrap();
        let zero = gamma.get("zero").unwrap().clone().unwrap();

        assert_eq!(zero.get_type().unwrap(), nat);
    }

    #[test]
    fn test_dependant() {
        setup();
        let Context(gamma, _) = parse(String::from("vec.dk"));
        let cons = gamma.get("cons");

        println!("{:#?}", cons);
    }
}
