#![feature(register_tool)]
#![register_tool(flux)]

use std::cell::RefCell;

#[flux::sig(fn(&RefCell<i32{v: v >= 0}>) -> i32{v: v > 0})]
fn test(cell: &RefCell<i32>) -> i32 {
    *cell.borrow_mut() //~ ERROR postcondition
}
