#![allow(unused)]

#[flux::trusted]
fn access_grant<F: FnOnce() -> u32>(fun: F) -> u32 {
    unimplemented!()
}

pub fn try_enter<F: FnOnce() -> u32>(fun: F) -> u32 {
    access_grant(fun)
}

// -------------------------------------------------------
#[flux::trusted]
fn apply<A, F: FnOnce() -> A>(fun: F) -> A {
    unimplemented!()
}

#[flux::sig(fn (fun:_) -> u32[99])]
pub fn test<F: FnOnce() -> u32>(fun: F) -> u32 {
    access_grant(fun)
} //~ ERROR refinement type
