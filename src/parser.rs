use core::panic;
use std::{
    collections::{HashMap, HashSet},
    fs,
    rc::Rc, sync::Mutex,
};

use dedukti_parse::{
    term::{App, AppH},
    Command, Intro, Rule, Strict, Symb,
};


use crate::lnode::LNode;

type ParseResult<'a, T> = std::result::Result<Vec<T>, dedukti_parse::Error>;

#[derive(Debug, Clone)]
pub struct Rewrite(pub Rc<LNode>, pub Rc<LNode>);
#[derive(Debug, Clone)]
pub struct Context(pub HashMap<String, Rc<LNode>>, pub Vec<Rewrite>);


fn parse_rule(
    gamma: &mut HashMap<String, Rc<LNode>>,
    rule: Rule<&str, App<AppH<Symb<&str>, &str>>>,
) -> Rewrite {
    // Clone gamma to have a local context.
    let mut gamma = gamma.clone();
    for v in rule.ctx {
        let (vname, ty) = v;
        let ty = ty.map(|ty| map_to_node(&mut gamma, ty).unwrap());
        let node = Rc::new(LNode::new_bvar(ty.clone()));
        gamma.insert(vname.to_string(), node);
    }

    let lhs = map_to_node(&mut gamma, rule.lhs).unwrap();
    let rhs = map_to_node(&mut gamma, rule.rhs).unwrap();

    Rewrite(lhs, rhs)
}

fn map_to_node(
    gamma: &mut HashMap<String, Rc<LNode>>,
    app: App<AppH<Symb<&str>, &str>>,
) -> Option<Rc<LNode>> {
    let head = match app.head {
        AppH::Atom(Symb { path, name }) => {
            if name == "Type" {
                Some(Rc::new(LNode::Type))
            } else {
                gamma.get(name).map(|t| t.clone())
            }
        }
        AppH::Abst(x, t, body) => {
            let t = t.map(|t| {
                map_to_node(gamma, t.as_ref().clone()).expect("No type inference admitted.")
            });

            if let Some(t) = t.clone() {
                gamma.insert(x.to_owned(), t.clone());
            }

            let x = Rc::new(LNode::new_bvar(t));
            let body = map_to_node(gamma, body.as_ref().clone()).unwrap();
            let abs = Rc::new(LNode::new_abs(x.clone(), body));
            x.bind_to(abs.clone());

            Some(abs)
        }
        AppH::Prod(x, a, t) => {
            let a = map_to_node(gamma, a.as_ref().clone());

            match x {
                Some(x) => {
                    let mut gamma = gamma.clone();
                    // If product has name `x`, save it as a variable node with type `a`.
                    let a = Rc::new(LNode::new_bvar(a));
                    gamma.insert(x.to_string(), a.clone());
                    let t = map_to_node(&mut gamma, t.as_ref().clone()).unwrap();

                    let node = Rc::new(LNode::new_prod(a.clone(), t.clone()));

                    a.add_parent(node.clone());
                    t.add_parent(node.clone());

                    Some(node)
                }
                None => {
                    let a = Rc::new(LNode::new_bvar(a));
                    let t = map_to_node(gamma, t.as_ref().clone()).unwrap();

                    let node = Rc::new(LNode::new_prod(a.clone(), t.clone()));

                    a.add_parent(node.clone());
                    t.add_parent(node.clone());

                    Some(node)
                }
            }
        }
    };

    let mut res = head;
    // Apply all the arguments to the head node (left application)
    for arg in app.args {
        // TODO: if arg is a wildcard, skip
        let t = map_to_node(gamma, arg.clone());

        if let Some(t) = t {
            res = Some(Rc::new(LNode::new_app(res.unwrap(), t)));
        } else {
            panic!("Something wrong.")
        }
    }

    res
}

pub fn print_context(c: &Context) {
    let Context(gamma, _) = c;
    println!("{}", "-".repeat(37));
    println!("| {0: <10} | {1: <20} |", "Symbol", "Address");
    println!("{}", "-".repeat(37));
    for (key, ty) in gamma {
        println!("| {0: <10} | {1: <20p} |", key, *ty);
    }
    println!("{}", "-".repeat(37));
}

pub fn parse(cmds: String) -> Context {
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
                        let node = Rc::new(LNode::new_var(t));

                        gamma.insert(name.to_string(), node);
                    }
                    Intro::Definition(x, y) => {
                        if let Some(x) = x {
                            let t = map_to_node(&mut gamma, x);
                            let node = Rc::new(LNode::new_var(t));

                            gamma.insert(name.to_string(), node);

                            continue;
                        }

                        // TODO: add y to rewrite rules.
                        if let Some(y) = y {
                            let t = map_to_node(&mut gamma, y);
                            let node = Rc::new(LNode::new_var(t));

                            gamma.insert(name.to_string(), node);
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
    use std::fs;

    #[test]
    fn test_parse() {
        let file_path = "examples/nat.dk";
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
        let file_path = "examples/nat.dk";
        let cmds = fs::read_to_string(file_path);
        assert!(cmds.is_ok(), "Error reading file");
        let cmds = cmds.unwrap();

        let c = parse(cmds.to_string());
        print_context(&c);
        let Context(gamma, _) = c;

        let nat = gamma.get("Nat").unwrap();
        let zero = gamma.get("zero").unwrap();

        assert_eq!(zero.get_type().unwrap(), *nat);
    }

    #[test]
    fn test_dependant() {
        let file_path = "examples/vec.dk";
        let cmds = fs::read_to_string(file_path);
        assert!(cmds.is_ok(), "Error reading file");
        let cmds = cmds.unwrap();

        let Context(gamma, _) = parse(cmds.to_string());
        let cons = gamma.get("cons");

        println!("{:#?}", cons);
    }
}
