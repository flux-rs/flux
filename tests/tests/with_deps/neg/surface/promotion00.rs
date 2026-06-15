extern crate flux_core;

#[flux_rs::trusted]
#[flux_rs::sig(fn(&i32[@a], &i32[@b]) -> bool[a == b])]
fn my_eq(a: &i32, b: &i32) -> bool {
    a == b
}

#[flux_rs::sig(fn () -> bool[true])]
pub fn bad() -> bool {
    my_eq(&0, &1) //~ ERROR refinement type
}
