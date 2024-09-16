#[flux::sig(fn(x: i32) -> i32{v: v < x})]
pub fn inc(x: i32) -> i32 {
    x + 1 //~ ERROR refinement type error
}
