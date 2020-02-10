#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]

/**@ (x:{x == 0}, y:{y > x}) -> v:{v >= y} @*/
fn foo(x: i32, y: i32) -> i32 {
    x + y
}

fn main() {
    /**@ x:{x >= 0} @*/
    let x = 1;

    /**@ y:{y > 0} @*/
    let y = x + 1;

    /**@ z:{z > 0} @*/
    let z = foo(y, y + 1);
}
