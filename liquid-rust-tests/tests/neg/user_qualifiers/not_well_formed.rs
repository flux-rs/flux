#![feature(register_tool)]
#![register_tool(lr)]
#![feature(custom_inner_attributes)]

#![lr::qualifier(MyQ(x: int) -> x == a)] //~ ERROR cannot find value `a` in this scope
#![lr::qualifier(MyQ(x: int) -> x + 1)] //~ ERROR mismatched sorts

#[lr::ty(fn<n: int>(i32@n) -> i32@n)]
pub fn dummy(x: i32) -> i32 {
    x
}
