mod lgraph;
use lgraph::*;

fn main() {
    let mut g = LGraph::new();
    let var1 = Var;
    let abs1 = Abs(&var1);
    let var2 = Var;
    let abs2 = Abs(&var2);
    let app1 = App(&abs1, &abs1);
    let app2 = App(&abs2, &abs2);
    let root = App(&app1, &app2);

    g.add_node(root);
    g.add_node(app1);
    g.add_node(app2);
    g.add_node(abs2);
    g.add_node(var2);
    g.add_node(abs1);
    g.add_node(var1);

    match blind_check(&g) {
        Err(e) => {
            println!("{}", e);
        }

        Ok(_) => {
            println!("Blind check completed.");
        }
    }
}
