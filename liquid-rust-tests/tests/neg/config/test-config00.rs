#![feature(register_tool)]
#![register_tool(lr)]
#![feature(custom_inner_attributes)]
#![lr::cfg(check_asserts = "assume", log_dir = "./log", dump_constraint = "do it!")] //~ ERROR invalid liquid configuration attribute: incorrect type in value for setting `dump_constraint`, expected bool

#[lr::sig(fn(x: i32, y: i32) -> i32)]
pub fn test(x: i32, y: i32) -> i32 {
    x / y
}