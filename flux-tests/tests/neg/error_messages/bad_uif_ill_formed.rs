#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::uf(fn foo(int, int) -> int)]

#[flux::assume]
#[flux::sig(fn(x: i32, y:i32) -> i32[foo(x)])] //~ ERROR this type takes 2 refinement parameters but 1 was found
pub fn foo(x: i32, y: i32) -> i32 {
    x + y
}

#[flux::sig(fn (i32[foo(10, 20, 30)]) -> i32)] //~ ERROR this type takes 2 refinement parameters but 3 were found
pub fn bar(a: i32) -> i32 {
    return a;
}
