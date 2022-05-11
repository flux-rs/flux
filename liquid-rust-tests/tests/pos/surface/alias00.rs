#![feature(register_tool)]
#![register_tool(lr)]
#![feature(custom_inner_attributes)]
#![lr::alias(type nat() = i32{v: 0 <= v})]
#![lr::alias(type lb(n) = i32{v: n <= v})]

#[lr::sig(fn(x:nat) -> nat)]
pub fn test1(x: i32) -> i32 {
    x + 1
}

#[lr::sig(fn(x:lb[10]) -> lb[10])]
pub fn test2(x: i32) -> i32 {
    x + 1
}
