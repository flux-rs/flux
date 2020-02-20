#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]

/**@ (x:{x >= 0}) -> v:{v >= x} @*/
fn foo(x: i32) -> i32 {
    x + 1
}

fn main() {
    let x = 1;

    if x >= 0 {
        let z = foo(x);
    } else {
        let z = foo(0 - x);
    }
}
