#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[lr::sig(fn() -> f64)]
pub fn float02() -> f64 {
    let mut vec = RVec::new();
    vec.push(0.1);
    *vec.get_mut(0) += 0.2;
    *vec.get(1) //~ ERROR precondition might not hold
}
