#![flux::opts(do_stuff = "true")] //~ ERROR invalid attribute: invalid crate cfg keyword `do_stuff`

#[flux::sig(fn(x: i32, y: i32) -> i32)]
pub fn test(x: i32, y: i32) -> i32 {
    x / y
}
