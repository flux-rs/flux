#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::dfn(even(x: int) -> bool { x == 0 || odd(x-1) })] //~ ERROR cycle
#![flux::dfn(odd(x: int) -> bool { x == 1 || even(x-1) })]

#[flux::sig(fn(x:i32) -> i32[x+1])]
pub fn test(x: i32) -> i32 {
    x + 1
}
