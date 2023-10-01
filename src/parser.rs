use core::panic;
use std::{collections::HashMap, fs, hash::Hash, rc::Rc};

use dedukti_parse::{
    term::{App, AppH},
    Command, Intro, Rule, Strict, Symb,
};

use crate::{lgraph::LGraph, lnode::LNode};

type Term<'a> = dedukti_parse::Term<Symb<&'a str>, &'a str>;
type Result<T> = std::result::Result<T, String>;
type ParseResult<'a, T> = std::result::Result<Vec<T>, dedukti_parse::Error>;

pub struct Rewrite(Rc<LNode>, Rc<LNode>);
pub struct Context(HashMap<String, Rc<LNode>>, Vec<Rewrite>);

fn parse_rule(
    gamma: &mut HashMap<String, Rc<LNode>>,
    rule: Rule<&str, App<AppH<Symb<&str>, &str>>>,
) -> Rewrite {
    // Clone gamma to have a local context.
    let mut gamma = gamma.clone();
    for v in rule.ctx {
        if let Some(ty) = v.1 {
            // TODO: use bound variables
            let ty = map_to_node(&mut gamma, ty);
            gamma.insert(v.0.to_string(), ty.unwrap());
        }
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
        AppH::Atom(sym) => {
            if sym.name == "Type" {
                Some(Rc::new(LNode::new_var(None)))
            } else {
                gamma.get(sym.name).map(|t| t.clone())
            }
        }
        AppH::Abst(x, t, body) => {
            let body = map_to_node(gamma, body.as_ref().clone()).unwrap();
            // bind x to t in gamma
            let t = t.map(|x| map_to_node(gamma, x.as_ref().clone()).unwrap());
            if let Some(t) = t {
                gamma.insert(x.to_owned(), t);
            }

            Some(Rc::new(LNode::new_abs(body)))
        }
        AppH::Prod(x, a, t) => {
            let a = map_to_node(gamma, a.as_ref().clone());
            match x {
                Some(x) => {
                    let mut gamma = gamma.clone();
                    // If product has name `x`, save it as a variable node with type `a`.
                    let a = Rc::new(LNode::new_var(a));
                    gamma.insert(x.to_string(), a.clone());
                    let t = map_to_node(&mut gamma, t.as_ref().clone()).unwrap();

                    let node = Rc::new(LNode::new_app(a.clone(), t.clone()));

                    a.add_parent(node.clone());
                    t.add_parent(node.clone());

                    Some(node)
                }
                None => {
                    let a = a.unwrap();
                    let t = map_to_node(gamma, t.as_ref().clone()).unwrap();
                    let node = Rc::new(LNode::new_app(a.clone(), t.clone()));

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
        // println!("{:#?}", arg);
        let t = map_to_node(gamma, arg.clone());
        if let Some(t) = t {
            res = Some(Rc::new(LNode::new_app(res.unwrap(), t)));
        } else {
            // TODO: if `t` is None, infer type from definition.
            panic!("Something wrong.")
        }
    }

    res
}

pub fn parse(cmds: String) -> Context {
    let parse: ParseResult<_> = Strict::<_, Symb<&str>, &str>::new(&cmds).collect();
    let parse = parse.unwrap();

    let mut gamma = HashMap::new();
    let mut rew_rules = Vec::new();
    for cmd in parse {
        match cmd {
            Command::Intro(name, _path, f) => match f {
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

                        // If a definition has a type, you can simply memorize its snf type (?).
                        continue;
                    }

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
            },
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
        let file_path = "examples/vec.dk";
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

        let Context(gamma, _) = parse(cmds.to_string());

        let nat = gamma.get("Nat").unwrap();
        let zero = gamma.get("zero").unwrap();
        let s = gamma.get("S").unwrap();
        let plus = gamma.get("plus").unwrap();

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
