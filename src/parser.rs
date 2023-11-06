use core::panic;
use std::{
    collections::{HashMap, HashSet},
    fmt::format,
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

fn parse_rule(
    mod_name: String,
    gamma: &mut HashMap<String, Option<Rc<LNode>>>,
    rew_rules: &mut Vec<Rewrite>,
    rule: Rule<&str, App<AppH<Symb<&str>, &str>>>,
) -> Rewrite {
    // Clone gamma to have a local context.
    // let mut gamma = gamma.clone();
    for v in rule.ctx {
        let (vname, ty) = v;
        let ty = ty.map(|ty| map_to_node(mod_name.clone(), gamma, rew_rules, ty).unwrap());
        let node = LNode::new_bvar(ty.clone());
        let name = format!("{mod_name}.{vname}");
        gamma.insert(name, Some(node));
    }

    let lhs = map_to_node(mod_name.clone(), gamma, rew_rules, rule.lhs).unwrap();
    let rhs = map_to_node(mod_name, gamma, rew_rules, rule.rhs).unwrap();

    Rewrite(lhs, rhs)
}

fn map_to_node(
    mod_name: String,
    gamma: &mut HashMap<String, Option<Rc<LNode>>>,
    rew_rules: &mut Vec<Rewrite>,
    app: App<AppH<Symb<&str>, &str>>,
) -> Option<Rc<LNode>> {
    let head = match app.head.clone() {
        AppH::Atom(Symb { path, name }) => {
            // start new parsing if `path` has not been encountered.
            let path_string = path.join(".");
            if !path.is_empty() && !OPEN_FILES.lock().unwrap().contains(&path_string) {
                OPEN_FILES.lock().unwrap().insert(path_string.clone());
                let filepath = format!("{path_string}.dk");
                let Context(_, new_rules) = parse(filepath, gamma);
                rew_rules.extend(new_rules);
            }

            if name == "Type" {
                Some(Rc::new(LNode::Type))
            } else {
                let name = if path.is_empty() {
                    format!("{mod_name}.{name}")
                } else {
                    format!("{path_string}.{name}")
                };

                let term = gamma.get(&name).map(|t| t.clone());
                term.unwrap_or_else(|| panic!("Symbol {:?} not in context", name))
            }
        }
        AppH::Abst(x, t, body) => {
            let t = t.map(|t| {
                map_to_node(mod_name.clone(), gamma, rew_rules, t.as_ref().clone())
                    .expect("No type inference admitted.")
            });

            let node = LNode::new_bvar(t);
            let name = format!("{mod_name}.{x}");
            gamma.insert(name, Some(node.clone()));
            let body =
                map_to_node(mod_name.clone(), gamma, rew_rules, body.as_ref().clone()).unwrap();
            let abs = LNode::new_abs(node.clone(), body);

            Some(abs)
        }
        AppH::Prod(x, a, t) => {
            let a = map_to_node(mod_name.clone(), gamma, rew_rules, a.as_ref().clone());

            match x {
                Some(x) => {
                    // FIXME: Stesso bug per il parsing.
                    // let mut gamma = gamma.clone();
                    // If product has name `x`, save it as a variable node with type `a`.
                    let a = LNode::new_bvar(a);
                    let name = format!("{mod_name}.{x}");
                    gamma.insert(name, Some(a.clone()));
                    let t = map_to_node(mod_name.clone(), gamma, rew_rules, t.as_ref().clone())
                        .unwrap();

                    let node = LNode::new_prod(a.clone(), t.clone());

                    Some(node)
                }
                None => {
                    let a = LNode::new_bvar(a);
                    let t = map_to_node(mod_name.clone(), gamma, rew_rules, t.as_ref().clone())
                        .unwrap();

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
            map_to_node(mod_name.clone(), gamma, rew_rules, arg.clone())
                .expect("Something went wrong")
        };

        res = Some(LNode::new_app(res.unwrap(), node));
    }

    res
}

pub fn print_context(gamma: &HashMap<String, Option<Rc<LNode>>>) {
    println!("{}", "-".repeat(57));
    println!("| {0: <30} | {1: <20} |", "Symbol", "Address");
    println!("{}", "-".repeat(57));
    for (key, ty) in gamma {
        if let Some(ty) = ty {
            println!("| {0: <30} | {1: <20p} |", key, *ty);
        } else {
            println!("| {0: <30} | {1: <20} |", key, "None");
        }
    }
    println!("{}", "-".repeat(57));
}

pub fn parse(filepath: String, gamma: &mut HashMap<String, Option<Rc<LNode>>>) -> Context {
    let cmds = fs::read_to_string(&filepath);
    let cmds = cmds.expect("File not found.");

    println!("Trying to parse {filepath:?}");
    let parse: ParseResult<_> = Strict::<_, Symb<&str>, &str>::new(&cmds).collect();
    let parse = parse.unwrap();

    let mut rew_rules = Vec::new();
    let mod_name = filepath
        .strip_suffix(".dk")
        .expect("File has not `.dk` extension.")
        .to_string();

    for cmd in parse {
        // dbg!(&cmd);
        match cmd.clone() {
            Command::Intro(name, app_terms, it) => {
                let name = format!("{mod_name}.{name}");
                for (name, node) in &app_terms {
                    let term = map_to_node(mod_name.clone(), gamma, &mut rew_rules, node.clone());
                    let name = format!("{mod_name}.{name}");
                    gamma.insert(name, term);
                }

                let term = match it {
                    Intro::Declaration(x) => {
                        let t = map_to_node(mod_name.clone(), gamma, &mut rew_rules, x);
                        let node = LNode::new_var(t);

                        node.clone()

                        // gamma.insert(name.to_string(), Some(node.clone()));
                    }
                    Intro::Definition(x, y) => {
                        // if Some(x) = x => t = map_to_node(..), altrimenti è None (caso di
                        // inferenza da checkare con bidirectional type_check).
                        let ty = x.map(|x| {
                            map_to_node(mod_name.clone(), gamma, &mut rew_rules, x)
                                .expect("Error encountered")
                        });
                        let node = LNode::new_var(ty);

                        // println!("[ INFO ] Inserting {name:?} symbol ");
                        // gamma.insert(name.to_string(), Some(node.clone()));

                        // if `def x := ...`, add y to rewrite rules.
                        if let Some(y) = y {
                            // FIXME: Se in y ci sono delle definizioni che scaturiscono nuovi
                            // parse, gamma non viene modificato per via del clone.
                            // let mut gamma = gamma.clone();
                            let lhs = node.clone();
                            // let rhs = map_to_node(mod_name.clone(), &mut gamma, y).unwrap();
                            let rhs =
                                map_to_node(mod_name.clone(), gamma, &mut rew_rules, y).unwrap();
                            rew_rules.push(Rewrite(lhs, rhs));
                        }

                        node
                    }
                    Intro::Theorem(ty, _) => {
                        let ty = map_to_node(mod_name.clone(), gamma, &mut rew_rules, ty).unwrap();
                        ty
                    }
                };

                let mut res = term;
                for (name, _) in app_terms {
                    let name = format!("{mod_name}.{name}");
                    let term = gamma.get(&name).unwrap().clone().unwrap();

                    res = LNode::new_app(res, term);
                }

                gamma.insert(name, Some(res));
            }
            Command::Rules(rules) => {
                let mut rules = rules
                    .iter()
                    .map(|rule| parse_rule(mod_name.clone(), gamma, &mut rew_rules, rule.clone()))
                    .collect();

                rew_rules.append(&mut rules);
            }
        }
    }

    // Context(gamma.clone(), rew_rules)
    Context(gamma.to_owned(), rew_rules)
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

        let c = parse(file_path.to_string(), &mut HashMap::new());
        let Context(gamma, _) = c;
        print_context(&gamma);

        let nat = gamma.get("nat.Nat").unwrap().clone().unwrap();
        let zero = gamma.get("nat.zero").unwrap().clone().unwrap();

        assert_eq!(zero.get_type().unwrap(), nat);
    }

    #[test]
    fn test_dependant() {
        setup();
        let Context(gamma, _) = parse(String::from("vec.dk"), &mut HashMap::new());
        let cons = gamma.get("vec.cons");

        println!("{:#?}", cons);
    }
}
