#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn() -> f64)]
pub fn float02() -> f64 {
    let mut vec = RVec::new();
    vec.push(0.1);
    vec[0] += 0.2;
    vec[0]
}
