// test that we allow moving out of a Box
pub fn mv(b: Box<Option<i32>>) -> Option<i32> {
    *b
}

// test that we allow binder under a box
#[flux::sig(fn(Box<i32[@n]>) -> i32[n+1])]
pub fn inc(b: Box<i32>) -> i32 {
    let x = *b;
    x + 1
}

// test that we allow binder under a box
#[flux::sig(fn(Box<i32[@n]>) -> Box<i32[n+1]>)]
pub fn inc_box(b: Box<i32>) -> Box<i32> {
    let x = *b;
    Box::new(x + 1)
}

// test that we match binder under a box
#[flux::sig(fn(n:i32) -> i32[n+1])]
pub fn inc_test(n: i32) -> i32 {
    let b0 = Box::new(n);
    let b1 = inc_box(b0);
    *b1
}

// update through a box
#[flux::sig(fn() -> i32[2])]
pub fn update() -> i32 {
    let mut x = Box::new(1);
    *x += 1;
    *x
}
