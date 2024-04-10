#![flux::defs {
    qualifier MyQ(x: int) { x == a } //~ ERROR cannot find name `a` in this scope
}]

#[flux::sig(fn(i32[@n]) -> i32[n])]
pub fn dummy(x: i32) -> i32 {
    x
}
