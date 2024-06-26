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

    0
}
