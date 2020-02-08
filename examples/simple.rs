#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]

fn foo(x: i32) {}

fn main() {
    /**@ x:{x >= 0} @*/
    let x = 1;

    /**@ y:{y > 0} @*/
    let y = x + 1;

    let z = foo(3);
}
