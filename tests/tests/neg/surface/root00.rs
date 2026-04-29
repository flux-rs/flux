#[flux::sig(fn(x: i32{x > 0}) -> i32{v: v > x})]
#[flux::root]
fn inc_positive(x: i32) -> i32 {
    x + 1
}

fn caller() -> i32 {
    inc_positive(-1) //~ ERROR refinement type
}
