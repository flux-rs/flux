use std::iter::Enumerate;

use flux_rs::extern_spec;

#[extern_spec(std::slice)]
impl<'a, T> Iterator for Iter<'a, T> {
    #[sig(fn(Iter<T>) -> Enumerate<Iter<T>>)]
    fn enumerate(self) -> Enumerate<Iter<'a, T>>; //~ERROR invalid extern spec
}
