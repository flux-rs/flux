// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 1
// suggestion: fn(u32[@n], &crate::rvec::RVec<u8>, u32[@n_1])
#![flux::opts(check_overflow = "strict")]

#[path = "../../lib/rvec.rs"]
mod rvec;

use rvec::RVec;

const LINEAR_MEM_SIZE: u32 = 100;

#[flux::alias(type SboxPtr[n: int] = u32[n])]
type SboxPtr = u32;

#[flux::trusted]
#[flux::sig(fn(dst: SboxPtr{dst + n < LINEAR_MEM_SIZE}, &RVec<u8>{sz: n <= sz}, n: u32))]
fn memcpy_to_sandbox(_: SboxPtr, _: &RVec<u8>, _: u32) {}

#[flux::sig(fn(SboxPtr, &RVec<u8>, u32) -> Result<(), ()>)]
fn copy_buf_to_sandbox(dst: SboxPtr, src: &RVec<u8>, n: u32) -> Result<(), ()> {
    if src.len() < n as usize || dst + n >= LINEAR_MEM_SIZE { //~ ERROR arithmetic operation may overflow
        return Err(());
    }
    memcpy_to_sandbox(dst, src, n);
    Ok(())
}
