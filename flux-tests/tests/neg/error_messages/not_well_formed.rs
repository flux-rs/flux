#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::qualifier(MyQ(x: int): x == a)] //~ ERROR cannot find value `a` in this scope
#![flux::qualifier(MyQ(x: int): x + 1)] //~ ERROR mismatched sorts

#[flux::sig(fn(i32[@n]) -> i32[n])]
pub fn dummy(x: i32) -> i32 {
    x
}
