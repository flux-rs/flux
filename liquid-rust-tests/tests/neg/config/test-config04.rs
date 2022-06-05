#![feature(register_tool)]
#![register_tool(lr)]
#![feature(custom_inner_attributes)]
#![lr::cfg(check_asserts = "assume", log_dir = "./log", check_asserts = "ignore")] //~ ERROR invalid liquid configuration: duplicated setting `check_asserts`

#[lr::sig(fn(x: i32, y: i32) -> i32)]
pub fn test(x: i32, y: i32) -> i32 {
    x / y
}
