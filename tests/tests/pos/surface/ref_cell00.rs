#![feature(allocator_ext, try_trait_v2)]

#[path = "../../lib/parametric_std.rs"]
mod parametric_std;

use std::cell::RefCell;

#[flux::sig(fn(&RefCell<i32{v: v >= 0}>) -> i32{v: v >= 0})]
fn test(cell: &RefCell<i32>) -> i32 {
    *cell.borrow_mut()
}
