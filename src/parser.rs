use core::panic;
use std::{
    collections::{HashMap, HashSet},
    fmt::format,
    fs,
    rc::Rc,
    sync::Mutex,
};

use crate::lnode::LNode;
use dedukti_parse::{
    term::{App, AppH},
    Command, Intro, Lazy, Rule, Strict, Symb,
};
use indicatif::{ProgressBar, ProgressIterator, ProgressStyle};
use lazy_static::lazy_static;
use log::info;

type ParseResult<'a, T> = std::result::Result<Vec<T>, dedukti_parse::Error>;

#[derive(Debug, Clone)]
pub struct Rewrite(pub Rc<LNode>, pub Rc<LNode>);
#[derive(Debug, Clone)]
pub struct Context(
    pub HashMap<String, Rc<LNode>>,
    pub HashMap<usize, Vec<Rewrite>>,
);

lazy_static! {
    static ref OPEN_FILES: Mutex<HashSet<String>> = Mutex::new(HashSet::new());
}

pub fn get_head(term: Rc<LNode>) -> Rc<LNode> {
    match &*term {
        LNode::App { left, .. } => get_head(left.clone()),
        _ => term,
    }
}

// def X: ...
//
// [ X ] 

fn parse_rule(
    mod_name: String,
    gamma: &mut HashMap<String, Rc<LNode>>,
    rew_rules: &mut HashMap<usize, Vec<Rewrite>>,
    rule: Rule<String, App<AppH<Symb<String>, String>>>,
) -> Rewrite {
    // Clone gamma to have a local context.
    let mut prev_symbols = HashMap::new();
    for v in rule.ctx.clone() {
        let (vname, ty) = v;
        let ty = ty.map(|ty| map_to_node(mod_name.clone(), gamma, rew_rules, ty).unwrap());
        let node = LNode::new_meta_var(ty.clone(), Some(&vname));
        let name = format!("{mod_name}.{vname}");
        if let Some(term) = gamma.get(&name) {
            prev_symbols.insert(name.clone(), term.clone());
        }
        gamma.insert(name, node);
    }

    let lhs = map_to_node(mod_name.clone(), gamma, rew_rules, rule.lhs).unwrap();
    let rhs = map_to_node(mod_name.clone(), gamma, rew_rules, rule.rhs).unwrap();

    rule.ctx.into_iter().for_each(|(vname, _)| {
        let name = format!("{mod_name}.{vname}");
        gamma.remove(&name);
    });

    gamma.extend(prev_symbols);
    Rewrite(lhs, rhs)
}

fn map_to_node(
    mod_name: String,
    gamma: &mut HashMap<String, Rc<LNode>>,
    rew_rules: &mut HashMap<usize, Vec<Rewrite>>,
    app: App<AppH<Symb<String>, String>>,
) -> Option<Rc<LNode>> {
    let head = match app.head.clone() {
        AppH::Atom(Symb { path, name }) => {
            // start new parsing if `path` has not been encountered.
            let path_string = path.join(".");
            if !path.is_empty() && !OPEN_FILES.lock().unwrap().contains(&path_string) {
                let filepath = format!("{path_string}.dk");
                
                // Extend gamma with the new definitions in `gamma_new`.
                let Context(_, new_rules) = parse(filepath, gamma);

                // Extend rewrite rules.
                for (head, head_rules) in new_rules {
                    for rule in head_rules {
                        // If I am extending the set of rules previously defined, push the new
                        // rule.
                        if let Some(rules) = rew_rules.get_mut(&head) {
                            rules.push(rule);
                        } else {
                            rew_rules.insert(head, vec![rule]);
                        }
                    }
                }
            }

            if name == "Type" {
                Some(Rc::new(LNode::Type))
            } else {
                let name = if path.is_empty() {
                    format!("{mod_name}.{name}")
                } else {
                    format!("{path_string}.{name}")
                };

                gamma.get(&name).map(|t| t.clone())
            }
        }
        AppH::Abst(x, t, body) => {
            let t = t.map(|t| {
                map_to_node(mod_name.clone(), gamma, rew_rules, t.as_ref().clone())
                    .expect("No type inference admitted.")
            });

            let name = format!("{mod_name}.{x}");
            let node = LNode::new_bvar(t, Some(&name));

            let prev_symb = gamma.get(&name).cloned();
            gamma.insert(name.clone(), node.clone());
            let body =
                map_to_node(mod_name.clone(), gamma, rew_rules, body.as_ref().clone()).unwrap();

            gamma.remove(&name);
            if let Some(term) = prev_symb {
                gamma.insert(name, term);
            }

            let abs = LNode::new_abs(node.clone(), body);

            Some(abs)
        }
        AppH::Prod(x, a, t) => {
            let a = map_to_node(mod_name.clone(), gamma, rew_rules, a.as_ref().clone());

            match x {
                Some(x) => {
                    let name = format!("{mod_name}.{x}");
                    let a = LNode::new_bvar(a, Some(&name));
                    // let gamma = &mut gamma.clone();

                    let prev_symb = gamma.get(&name).cloned();
                    gamma.insert(name.clone(), a.clone());
                    let t = map_to_node(mod_name.clone(), gamma, rew_rules, t.as_ref().clone())
                        .unwrap();

                    gamma.remove(&name);
                    if let Some(term) = prev_symb {
                        gamma.insert(name, term);
                    }

                    let node = LNode::new_prod(a.clone(), t.clone());

                    Some(node)
                }
                None => {
                    let a = LNode::new_bvar(a, None);
                    let t = map_to_node(mod_name.clone(), gamma, rew_rules, t.as_ref().clone())
                        .unwrap();

                    let node = LNode::new_prod(a, t.clone());

                    Some(node)
                }
            }
        }
    };

    let mut res = head;
    // Apply all the arguments to the head node (left application)
    for arg in &app.args {
        // if arg is a wildcard, apply a var on which you can infer
        let node = match &arg.head {
            AppH::Atom(Symb { name, .. }) if name == "_" => LNode::new_meta_var(None, Some("_")),
            _ => map_to_node(mod_name.clone(), gamma, rew_rules, arg.clone())
                .expect("Something went wrong"),
        };

        let head = res.clone().unwrap_or_else(|| panic!("Error in {:?}", app));
        res = Some(LNode::new_app(head, node));
    }

    res
}

pub fn parse(filepath: String, gamma: &mut HashMap<String, Rc<LNode>>) -> Context {
    let cmds = fs::read_to_string(&filepath);
    let cmds = cmds.expect("File not found.");

    // let parse: ParseResult<_> = Strict::<_, Symb<&str>, &str>::new(&cmds).collect();
    let parse: ParseResult<_> = Lazy::<_, Symb<String>, String>::new(cmds.lines()).collect();
    let parse = parse.unwrap();

    let mut rew_rules = HashMap::new();
    let mod_name = filepath
        .strip_suffix(".dk")
        .expect("File has not `.dk` extension.")
        .to_string();
    OPEN_FILES.lock().unwrap().insert(mod_name.clone());

    let bar = ProgressBar::new(parse.len() as u64);
    bar.set_message(filepath.clone());
    bar.set_style(
        ProgressStyle::default_bar()
        .template("[ Parsing {msg} ] {bar:>40}")
        .unwrap()
        .progress_chars("#-"),
    );
    for cmd in parse {
        bar.inc(1);

        match cmd.clone() {
            Command::Intro(name, app_terms, it) => {
                let name_mod = format!("{mod_name}.{name}");

                for (name, node) in &app_terms {
                    let typ = map_to_node(mod_name.clone(), gamma, &mut rew_rules, node.clone());
                    let term = LNode::new_bvar(typ, Some(name));
                    let name = format!("{mod_name}.{name}");
                    gamma.insert(name, term);
                }

                let term = match it {
                    Intro::Declaration(x) => {
                        let t = map_to_node(mod_name.clone(), gamma, &mut rew_rules, x);
                        let node = LNode::new_var(t, &name_mod);

                        node.clone()
                    }
                    Intro::Definition(x, y) => {
                        // if Some(x) = x => t = map_to_node(..), altrimenti è None (caso di
                        // inferenza da checkare con bidirectional type_check).
                        let ty = x.map(|x| {
                            map_to_node(mod_name.clone(), gamma, &mut rew_rules, x)
                                .expect("Error encountered")
                        });
                        let node = LNode::new_var(ty, &name_mod);

                        // if `def x := ...`, add y to rewrite rules.
                        if let Some(y) = y {
                            let lhs = node.clone();
                            let rhs =
                                map_to_node(mod_name.clone(), gamma, &mut rew_rules, y).unwrap();
                            rew_rules.insert(
                                Rc::into_raw(node.clone()) as usize,
                                vec![Rewrite(lhs, rhs)],
                            );

                            // rew_rules.push(Rewrite(lhs, rhs));
                        }

                        node
                    }
                    Intro::Theorem(ty, _) => {
                        let ty = map_to_node(mod_name.clone(), gamma, &mut rew_rules, ty).unwrap();
                        ty
                    }
                };

                let mut res = term;
                for (name, _) in app_terms.iter().rev() {
                    let name = format!("{mod_name}.{name}");
                    let term = gamma.get(&name).unwrap().clone();
                    gamma.remove(&name);
                    res = LNode::new_abs(term, res);
                }

                // println!("Inserted {:?}", res);
                gamma.insert(name_mod, res);
            }
            Command::Rules(rules) => {
                let rules: Vec<_> = rules
                    .iter()
                    .map(|rule| parse_rule(mod_name.clone(), gamma, &mut rew_rules, rule.clone()))
                    .collect();

                // println!("{:#?}", gamma);
                for Rewrite(lhs, rhs) in rules {
                    let head = get_head(lhs.clone());
                    let head = Rc::into_raw(head) as usize;

                    // If head is already in `rew_rules`, append new rule
                    if let Some(rules) = rew_rules.get_mut(&head) {
                        rules.push(Rewrite(lhs, rhs));
                    } else {
                        rew_rules.insert(head, vec![Rewrite(lhs, rhs)]);
                    }
                }
            }
        }
    }

    bar.finish_with_message(filepath.clone());
    Context(gamma.clone(), rew_rules)
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
        let Context(gamma, rules) = c;

        let nat = gamma.get("nat.Nat").unwrap().clone();
        let zero = gamma.get("nat.zero").unwrap().clone();
        let k2 = gamma.get("nat.K2").unwrap().clone();
        let k2_ptr = Rc::into_raw(k2) as usize;
        let rules = rules.get(&k2_ptr);
        info!("{:?}", rules);

        assert_eq!(zero.get_type().unwrap(), nat);
    }
}
