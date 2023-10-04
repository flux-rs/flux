#![flux::defs {
    qualifier MyQ1(x: int, a: int) { x == a }
    qualifier MyQ2(x: int) { x > 1 }
}]

#[flux::sig(fn(i32[@n]) -> i32[n])]
pub fn dummy(x: i32) -> i32 {
    x
}
