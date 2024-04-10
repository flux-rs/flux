#[path = "../../lib/pair.rs"]
mod pair;
use pair::Pair;

#[flux::sig(fn(bool[true]) -> i32[0])]
pub fn assert(_b: bool) -> i32 {
    0
}

#[flux::sig(fn(Pair) -> i32[0])]
pub fn opaque_struct_01(p: Pair) -> i32 {
    let fst = p.fst();
    let snd = p.snd();
    assert(snd - fst > 0); //~ ERROR refinement type error
    0
}
