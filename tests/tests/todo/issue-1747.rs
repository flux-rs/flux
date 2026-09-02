extern crate flux_core;

use flux_rs::*;

#[extern_spec(core::iter)]
#[assoc(fn valid_item(x: Enumerate<I>, item: (int, <I as Iterator>::Item)) -> bool {
    x.idx <= item.0
})]
impl<I: Iterator> Iterator for core::iter::Enumerate<I> {
    fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)>;
}
