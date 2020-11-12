#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_doc_comments)]

fn abs(mut n: u32) -> u32 {
    if n < 0 {
        n = 0 - n;
    }
    return n;
}

fn main() {}
