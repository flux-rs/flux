#![flux::defs {
    // A wildcard is instantiated with literal constants, so it needs a sort that has them.
    qualifier BadWild(x: int, a #: bool) { a => x > 0 } //~ ERROR wildcard parameter cannot have sort
}]

#[flux::sig(fn(i32[@n]) -> i32[n])]
pub fn dummy(x: i32) -> i32 {
    x
}
