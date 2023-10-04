#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn () -> RVec<u8>[5])]
pub fn test() -> RVec<u8> {
    let mut src: RVec<u8> = rvec![1, 2, 3];
    let bytes: [u8; 2] = [4, 5];
    src.extend_from_slice(&bytes);
    src
}
