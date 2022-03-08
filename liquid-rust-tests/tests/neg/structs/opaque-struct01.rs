#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/pair.rs"]
mod pair;
use pair::Pair;

#[lr::ty(fn(bool @ true) -> i32@0)]
pub fn assert(_b: bool) -> i32 {
    0
}

#[lr::ty(fn(Pair) -> i32@0)]
pub fn opaque_struct_01(p: Pair) -> i32 {
    let fst = p.fst();
    let snd = p.snd();
    assert(snd - fst > 0); //~ ERROR precondition might not hold
    0
}
