#![feature(register_tool)]
#![register_tool(lr)]
#![feature(custom_inner_attributes)]
#![lr::cfg(check_asserts = "assume", do_stuff = "true")] //~ ERROR invalid liquid configuration attribute: invalid crate cfg keyword `do_stuff`

#[lr::sig(fn(x: i32, y: i32) -> i32)]
pub fn test(x: i32, y: i32) -> i32 {
    x / y
}