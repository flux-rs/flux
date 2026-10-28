extern crate flux_core;

pub fn a<T>(x: &T) -> T {
    unsafe { ptr::read(x) } 
}

pub fn b(x: &u32) -> u32 {
    unsafe { ptr::read(x) }
}
