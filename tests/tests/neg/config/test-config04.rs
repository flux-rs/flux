#![flux::opts(log_dir = "./log1", log_dir = "./log2")] //~ ERROR invalid attribute: duplicated key `log_dir`

#[flux::sig(fn(x: i32, y: i32) -> i32)]
pub fn test(x: i32, y: i32) -> i32 {
    x / y
}
