#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::defs {
    fn foo(n:int) -> bool;
    fn bar(n:int) -> bool { foo(n) }
}]

fn is_foo(n: i32) -> bool {
    n > 10
}

#[flux::sig(fn(n:i32) -> bool[bar(n)])]
fn is_bar(n: i32) -> bool {
    is_foo(n) //~ ERROR refinement type
}
