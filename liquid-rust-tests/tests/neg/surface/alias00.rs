#![feature(register_tool)]
#![register_tool(lr)]
#![lr::def(type nat = i32{v: 0 <= v})]

#[lr::sig(fn(x:nat) -> nat)]
pub fn inc(x: i32) -> i32 { //~ ERROR postcondition might not hold
    x - 1
}
