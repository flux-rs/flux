// configure check for the entire thing
#![cfg_attr(flux, flux::opts(check_overflow = "strict"))]

const MAX: u32 = std::u32::MAX;

#[flux::sig(fn(u32[@x], u32[@y]) -> u32[x + y] requires x + y <= MAX)]
fn add(x: u32, y: u32) -> u32 {
    x + y
}

#[flux::opts(check_overflow = "none")]
fn add_more(x: u32, y: u32, z: u32) -> u32 {
    x + y + z
}
