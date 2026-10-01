#[flux::spec(fn(x: i32[@n]) -> i32[n + 1])]
pub fn inc(x: i32) -> i32 {
    x + 1
}

#[flux::spec(fn(x: i32) -> i32[x + 3])]
pub fn inc_twice(x: i32) -> i32 {
    inc(inc(x)) //~ ERROR refinement type
}

#[flux::spec(fn(a: usize, b: usize, f: F) -> usize{v: v <= a + b} where F: FnOnce(usize) -> usize{v: v <= a})]
pub fn mixed<F: FnOnce(usize) -> usize>(a: usize, b: usize, f: F) -> usize {
    f(0) + b
}

pub fn use_mixed() -> usize {
    mixed(5, 6, |_| 6) //~ ERROR refinement type
}
