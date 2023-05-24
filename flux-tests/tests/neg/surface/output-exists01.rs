#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;

use rvec::RVec;

#[flux::sig(
    fn(x: &strg i32[@n], y: &strg i32[n], bool)
    ensures x: i32[#m], y: i32[m]
)]
fn test00(x: &mut i32, y: &mut i32, b: bool) {
    if b {
        //~^ ERROR refinement
        *x += 1;
        *y -= 1;
    } else {
        //~^ ERROR refinement type
        *x -= 1;
        *y += 1;
    }
}

#[flux::sig(
    fn(x: &strg RVec<i32>[@n], y: &strg RVec<i32>[n])
    ensures x: RVec<i32>[#m], y: RVec<i32>[m]
)]
fn test01(x: &mut RVec<i32>, y: &mut RVec<i32>) {
    if x.len() == 10 {
        x.pop();
        y.pop();
    } else {
        //~^ ERROR refinement type
        x.push(10);
    }
}

fn random() -> bool {
    false
}

#[flux::sig(
    fn(x: &strg i32[@n], y: &strg i32[n])
    ensures x: i32[#m], y: i32[m]
)]
fn test02(x: &mut i32, y: &mut i32) {
    while random() {
        //~^ ERROR refinement type
        *x += 1;
    }
}
