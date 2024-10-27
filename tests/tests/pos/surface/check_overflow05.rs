// configure check for the entire thing
#![cfg_attr(flux, flux::cfg(check_overflow = true))]

const MAX: u32 = std::u32::MAX;

#[flux::sig(fn(u32[@x], u32[@y]) -> u32[x + y] requires x + y <= MAX)]
fn add(x: u32, y: u32) -> u32 {
    x + y
}

#[flux::check_overflow(no)]
fn add_more(x: u32, y: u32, z: u32) -> u32 {
    x + y + z
}
