#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::cfg(log_dir = "./log", dump_constraint = "do it!")] //~ ERROR invalid flux configuration: incorrect type in value for setting `dump_constraint`, expected bool

#[flux::sig(fn(x: i32, y: i32) -> i32)]
pub fn test(x: i32, y: i32) -> i32 {
    x / y
}
