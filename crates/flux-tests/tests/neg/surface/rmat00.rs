#![allow(unused_attributes)]

#[path = "../../lib/rmat.rs"]
pub mod rmat;
use rmat::RMat;

#[flux::sig(fn() -> i32)]
pub fn test() -> i32 {
    let pi: f32 = 3.14;
    let mut m = RMat::new(5, 10, pi);

    let v1 = *m.get(3, 7);
    *m.get_mut(4, 8) = v1 + v1;

    let v2 = *m.get(3, 17); //~ ERROR refinement type error
    *m.get_mut(14, 8) = v2 + v2; //~ ERROR refinement type error

    0
}
