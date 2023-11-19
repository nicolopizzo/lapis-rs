#![allow(dead_code)]
#![allow(unused_imports)]
use core::panic;
use std::{collections::HashMap, env, process::exit};

use parser::{Context, Rewrite};

use crate::{check::check_context, parser::parse};

mod check;
mod lgraph;
mod lnode;
mod parser;
mod utils;
fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() <= 1 {
        println!("ERROR: YOU MUST SPECIFY A TARGET FILE");
        println!("Example usage: lapis <FILEPATH>");
    }

    let filepath = &args[1];
    let idx = filepath.rfind("/");
    if let Some(idx) = idx {
        let path = &filepath[0..idx];
        if let Err(e) = env::set_current_dir(path) {
            panic!("Error: {:?}", e);
        }
    }

    let idx = idx.unwrap_or(0);
    let filename = &filepath[idx + 1..];

    let ctx = parse(filename);
    let check = check_context(ctx);

    if let Err(e) = check {
        println!("Error occurred: {:?}", e);
    }
}
