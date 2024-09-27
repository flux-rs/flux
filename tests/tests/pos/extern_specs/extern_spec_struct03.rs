// Testing we can add external specs to "transparent" structs.

use flux_rs::extern_spec;

#[extern_spec(std::ops)]
#[refined_by(start: Idx, end: Idx)]
struct Range<Idx> {
    #[field(Idx[start])]
    start: Idx,
    #[field(Idx[end])]
    end: Idx,
}

#[extern_spec(std::ops)]
#[generics(Idx as base)]
impl<Idx: PartialOrd<Idx>> Range<Idx> {
    // This specification is actually unsound for `Idx`s where the `PartialOrd` implementation doesn't
    // match the logical `<`.
    #[sig(fn(&Range<Idx>[@r]) -> bool[!(r.start < r.end)])]
    fn is_empty(&self) -> bool;
}

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

fn test00() {
    let r = 0..1;
    assert(!r.is_empty());
}
