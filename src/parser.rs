use std::rc::Rc;

use dedukti_parse::{
    term::{self, App, AppH},
    Command, Intro, Strict, Symb,
};

use crate::lnode::LNode;

type Term<'a> = dedukti_parse::Term<Symb<&'a str>, &'a str>;
type Result<T> = std::result::Result<T, String>;
type ParseResult<'a, T> = std::result::Result<Vec<T>, dedukti_parse::Error>;

fn map_to_node(app: App<AppH<Symb<&str>, &str>>) -> Rc<LNode> {
    match app.head {
        AppH::Atom(_name) => Rc::new(LNode::new_var(None)),
        AppH::Abst(_, _, _) => todo!(),
        AppH::Prod(x, a, t) => {
            // TODO: return a PI-node or an App-node?
            let l = map_to_node(a.as_ref().clone());
            let r = map_to_node(t.as_ref().clone());

            let node = Rc::new(LNode::new_app(l.clone(), r.clone(), None));

            l.add_parent(node.clone());
            r.add_parent(node.clone()); 

            node
        }
    }

}

pub fn parse(cmds: String) {
    let parse: ParseResult<_> = Strict::<_, Symb<&str>, &str>::new(&cmds).collect();
    let parse = parse.unwrap();

    let mut nodes = Vec::new();
    for cmd in parse {
        match cmd {
            Command::Intro(name, _path, f) => match f {
                Intro::Declaration(x) => {
                    let node = map_to_node(x);
                    println!("{}", name);
                    println!("{:?}\n", node);

                    nodes.push(node);
                }
                Intro::Definition(x, y) => {
                    if let Some(x) = x {
                        let node = map_to_node(x);
                        println!("{}", name);
                        println!("{:?}\n", node);
                        nodes.push(node);
                    }

                    // if let Some(y) = y {
                    //     let node = map_to_node(y);
                    //     println!("{}", name);
                    //     println!("{:?}\n", node);
                    //     nodes.push(node);
                    // }
                }
                Intro::Theorem(_, _) => todo!(),
            },
            Command::Rules(_) => todo!("Rule parsing"),
        }
    }
}

#[test]
fn test_parse() {
    let cmds = r#"
        Nat: Type.
        zero: Nat.
        def S: Nat -> Nat.
        def plus: Nat -> Nat -> Nat.
        [n: Nat] plus zero n --> n.
        [m: Nat,n : Nat] plus (S m) n --> S (plus m n).
    "#;

    parse(cmds.to_string());
}