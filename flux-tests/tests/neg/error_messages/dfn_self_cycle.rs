#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::defs {
    fn sum(n: int) -> int { n + sum(n-1) } //~ ERROR cycle
}]

#[flux::sig(fn(x:i32) -> i32[x+1])]
pub fn test(x: i32) -> i32 {
    x + 1
}
