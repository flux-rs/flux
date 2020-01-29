#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]

/**@ (x:{x > 0}) -> v:{true} @*/
fn only_pos(x: i32) {}

fn good() {
    /**@ x:{x == 3} @*/
    let x: i32 = 3;
    only_pos(x);
}

fn bad() {
    /**@ y:{y == 0} @*/
    let y: i32 = 0;
    only_pos(y);
}

fn main() {}
