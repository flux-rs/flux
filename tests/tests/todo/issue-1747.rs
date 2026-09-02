extern crate flux_core;

use flux_rs::*;

#[flux::sig(fn(bool[true]))]
fn assert(_b: bool) {}

#[extern_spec(core::iter)]
#[assoc(fn valid_item(x: Enumerate<I>, item: (int, <I as Iterator>::Item)) -> bool {
    x.idx <= item.0
})]
impl<I: Iterator> Iterator for core::iter::Enumerate<I> {
    fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)>;
}

fn check<I>(iter: I)
where
    I: Iterator<Item = bool>,
{
    iter.enumerate().for_each(|(i, _)| assert(i < 10));
}
