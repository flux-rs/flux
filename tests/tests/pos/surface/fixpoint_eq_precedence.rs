// Fixpoint parser has `=` at two different precedence levels depending on whether is used on
// booleans or not. This tests we are emitting the correct constraint in such cases.
#[flux::sig(fn(i32{v : false == false && v == 42}) -> i32[42])]
pub fn foo(x: i32) -> i32 {
    x
}
