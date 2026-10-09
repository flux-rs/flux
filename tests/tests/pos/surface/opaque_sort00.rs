#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

#[flux::sig(fn(b: bool, x: I::Item[@n], y: I::Item[@m]) -> I::Item[if b { n } else { m }])]
pub fn choose<I: Iterator>(b: bool, x: I::Item, y: I::Item) -> I::Item {
    if b { x } else { y }
}

pub fn test00() {
    assert(choose::<std::vec::IntoIter<i32>>(true, 0, 1) == 0);
}
