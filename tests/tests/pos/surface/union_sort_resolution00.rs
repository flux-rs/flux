// Test we can correctly resolve unions as sorts

#![allow(unused)]

use flux_attrs::*;

union MyUnion {
    x: i32,
}

#[refined_by(x: crate::MyUnion)]
struct UsesUnionSort {
    #[field(crate::MyUnion[x])]
    x: MyUnion,
}
