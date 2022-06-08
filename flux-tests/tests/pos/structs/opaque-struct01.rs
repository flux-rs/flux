#![feature(register_tool)]
#![register_tool(flux)]
#[path = "../../lib/pair.rs"]
mod pair;
use pair::Pair;

#[flux::sig(fn(bool[true]) -> i32[0])]
pub fn assert(_b: bool) -> i32 {
    0
}

#[flux::sig(fn(Pair, bool) -> i32[0])]
pub fn opaque_struct01(mut p: Pair, b: bool) -> i32 {
    if b {
        p.set_fst(0);
        p.set_snd(1);
    } else {
        p.set_fst(1);
        p.set_snd(2);
    }
    assert(p.snd() > p.fst());
    0
}
