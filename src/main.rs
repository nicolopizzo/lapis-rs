use std::{rc::Rc, fmt::Pointer};

mod lgraph;

#[derive(PartialEq)]
struct Foo {}

fn address_of<T: Pointer>(x: &T) -> u64 {
    let str_addr = format!("{:p}", x);
    u64::from_str_radix(str_addr.trim_start_matches("0x"), 16).unwrap()
}

fn main() {
    let x = 5;
    let y = x.clone();
    // let z = Rc::new(5);

    let px = address_of(&Box::new(x));
    let py = address_of(&Box::new(y));

    println!("{}, {}", px, py)

    // let k = Foo {};
    // let x = k;
    // let y = &Foo {};

    // println!("{}", x == y);
    // assert!(x == y);
    // assert_eq!(x, z);
    // println!("{}", x==z)
}
