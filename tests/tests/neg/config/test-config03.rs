#![flux::opts(fn(x: i32, y:i32) -> i32)] //~ ERROR invalid attribute: bad syntax

#[flux::sig(fn(x: i32, y: i32) -> i32)]
pub fn test(x: i32, y: i32) -> i32 {
    x / y
}
