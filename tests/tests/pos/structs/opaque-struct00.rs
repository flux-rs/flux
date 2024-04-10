#[path = "../../lib/pair.rs"]
mod pair;
use pair::Pair;

#[flux::sig(fn(bool[true]) -> i32[0])]
pub fn assert(_b: bool) -> i32 {
    0
}

#[flux::sig(fn() -> i32[0])]
pub fn opaque_struct00() -> i32 {
    let p = Pair::new(0, 1);
    let fst = p.fst();
    let snd = p.snd();
    assert(snd - fst > 0);
    0
}
