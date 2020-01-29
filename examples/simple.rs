#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]

/**@
(x:{x > 0}, y:{3 + 3}) -> v:{v > 0}
@*/
fn foo(x: i32, y: i32) {
    let x: f32 = 3.3;
    /**@ y:{x > y :: f32} @*/
    let y: f64 = 4.;

    /**@ s:{3 + 3} @*/
    let s = "hola";

    // let a = asdf;
}

fn main() {}
