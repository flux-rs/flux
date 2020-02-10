#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]

/**@ (x:{x == 0}) -> v:{v > x} @*/
fn foo(x: i32) -> i32 {
    x + 1
}

fn main() {
    /**@ x:{x >= 0} @*/
    let x = 1;

    /**@ y:{y > 0} @*/
    let y = x + 1;

    /**@ z:{z > 0} @*/
    let z = foo(y);
}
