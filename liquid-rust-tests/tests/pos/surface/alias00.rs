#![feature(register_tool)]
#![register_tool(lr)]
#![feature(custom_inner_attributes)]
#![lr::alias(nat<> -> i32{v: 0 <= v})]

#[lr::sig(fn(x:nat) -> nat)]
pub fn inc(x: i32) -> i32 {
    x + 1
}
