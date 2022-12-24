#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::def(foo(x:int, y:int) -> int)]

#[flux::sig(fn (i32[fog(10, 20)]) -> i32)] //~ ERROR cannot find value `fog`
pub fn baz(a: i32) -> i32 {
    return a;
}
