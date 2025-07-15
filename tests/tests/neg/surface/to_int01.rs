use flux_rs::attrs::*;

#[spec(fn (x:bool) -> u32[cast(x)])]
pub fn test_bool_to_int(_x: bool) -> u32 {
    0 //~ ERROR refinement type
}

#[spec(fn (x:bool) -> u32[cast(x)])]
pub fn test_bool_to_int_with_if(x: bool) -> u32 {
    if x { 1 } else { 1 } //~ERROR refinement type
}

struct S {}

#[flux::opts(allow_uninterpreted_cast = true)]
#[flux::sig(fn(x:S) -> i32[cast(x)])]
fn foo(x: S) -> i32 {
    0 //~ ERROR refinement type
}
