extern crate flux_core;
use flux_rs::assert;


pub fn test_saturating_usize(x: usize, y: usize, z: usize) {
    // Not true if x < y, as it saturates
    let sub = x - y; //~ ERROR arithmetic operation may underflow 
    assert(x.saturating_sub(y) == sub); //~ ERROR refinement type error
    // Not true if x + y > usize::MAX, as it saturates
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_saturating_u32(x: u32, y: u32, z: u32) {
    // Not true if x < y, as it saturates
    let sub = x - y; //~ ERROR arithmetic operation may underflow 
    assert(x.saturating_sub(y) == sub); //~ ERROR refinement type error
    // Not true if x + y > u32::MAX, as it saturates
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_saturating_u64(x: u64, y: u64, z: u64) {
    // Not true if x < y, as it saturates
    let sub = x - y; //~ ERROR arithmetic operation may underflow 
    assert(x.saturating_sub(y) == sub); //~ ERROR refinement type error
    // Not true if x + y > u64::MAX, as it saturates
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}
