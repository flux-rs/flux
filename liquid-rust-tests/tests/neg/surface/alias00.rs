#![feature(register_tool)]
#![register_tool(lr)]
#![feature(custom_inner_attributes)]
#![lr::alias(nat() -> i32{v: 0 <= v})]
#![lr::alias(lb(n) -> i32{v: n <= v})]

#[lr::sig(fn(x:nat[]) -> nat[])]
pub fn test1(x: i32) -> i32 { //~ ERROR postcondition might not hold
    x - 1
}

#[lr::sig(fn(x:lb[0]) -> lb[10])]
pub fn test2(x: i32) -> i32 { //~ ERROR postcondition might not hold
    x + 1
}
