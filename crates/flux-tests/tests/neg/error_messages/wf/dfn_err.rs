#![flux::defs {
    fn nat(x: int) -> bool { 0 <= x }
    fn bat(x: int) -> int  { 0 <= x } //~ ERROR mismatched sorts
}]

#[flux::sig(fn(x:i32{nat(x)}) -> i32{v:nat(v, v)})] //~ ERROR this function takes 1 refinement argument but 2 were found
pub fn test1(x: i32) -> i32 {
    x + 1
}

#[flux::sig(fn(x:i32) -> i32{v:nat(true)})] //~ ERROR mismatched sorts
pub fn test2(x: i32) -> i32 {
    x + 1
}

#[flux::sig(fn(x:i32) -> i32[nat(x) + 1])] //~ ERROR mismatched sorts
pub fn test3(x: i32) -> i32 {
    x + 1
}
