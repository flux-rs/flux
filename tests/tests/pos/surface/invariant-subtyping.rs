use std::cell::UnsafeCell;

fn test00() {
    test01(UnsafeCell::new(0), 0)
}

#[flux::sig(fn(UnsafeCell<i32[id]>, i32[@id]))]
fn test01(s: UnsafeCell<i32>, id: i32) {}
