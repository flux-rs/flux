// Test we can correctly resolve unions as sorts

#![allow(unused)]

use flux_attrs::*;

union MyUnion {
    x: i32,
}

#[refined_by(x: MyUnion)]
struct UsesUnionSort {
    #[field(MyUnion[x])]
    x: MyUnion,
}

