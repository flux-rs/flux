#![feature(register_tool)]
#![register_tool(flux)]
// Test definition and checking of const and qualifiers
#![feature(custom_inner_attributes)]
#![flux::qualifier(MyQ1(x: int, a: int): x == a + FORTY_TOO)] //~ ERROR cannot find

#[flux::constant]
const FORTY_TWO: usize = 21 + 21;

#[flux::sig(fn() -> bool[true])]
pub fn test0() -> bool {
    FORTY_TWO == 40 + 2
}
