#![feature(register_tool, box_patterns)]
#![register_tool(flux)]

// Fixpoint parser has `=` at two different precedence level dependeing on wether is used on booleans
// or not. This test checks we are emitting the correct constraint in such a case.
#[flux::sig(fn(i32{v : false == false && v == 42}) -> i32[42])]
pub fn foo(x: i32) -> i32 {
    x
}
