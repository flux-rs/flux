#[flux::sig(fn(Box<i32[@n]>) -> i32[n+1])]
pub fn inc(b: Box<i32>) -> i32 {
    let x = *b;
    x + 2 //~ ERROR refinement type
}

#[flux::sig(fn(Box<i32[@n]>) -> Box<i32[n+1]>)]
pub fn inc_box(b: Box<i32>) -> Box<i32> {
    let x = *b;
    Box::new(x + 10)
} //~ ERROR refinement type

#[flux::sig(fn(n:i32) -> i32[n+2])]
pub fn inc_test(n: i32) -> i32 {
    let b0 = Box::new(n);
    let b1 = inc_box(b0);
    *b1
} //~ ERROR refinement type

// update through a box
#[flux::sig(fn() -> i32[1])]
pub fn update() -> i32 {
    let mut x = Box::new(1);
    *x += 1;
    *x //~ ERROR refinement type
}
