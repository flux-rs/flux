#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/pair.rs"]
mod pair;
use pair::Pair;

#[flux::sig(fn(bool[true]) -> i32[0])]
pub fn assert(_b: bool) -> i32 {
    0
}

#[flux::sig(fn() -> i32[0])]
pub fn foo() -> i32 {
    let p = Pair::new(0, 0);
    let fst = p.fst();
    let snd = p.snd();
    assert(snd - fst > 0); //~ ERROR precondition might not hold
    0
}
