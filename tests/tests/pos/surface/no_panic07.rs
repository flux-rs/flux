struct MyIter<'a, T>(&'a T);

#[flux_rs::assoc(fn next_no_panic() -> bool)]
trait MyIterator {
    #[flux_rs::sig(fn(&mut Self) -> bool)]
    #[flux_rs::no_panic_if(Self::next_no_panic())]
    fn next(&mut self) -> bool;
}

#[flux_rs::assoc(fn next_no_panic() -> bool { true })]
impl<'a, T> MyIterator for MyIter<'a, T> {
    #[flux_rs::sig(fn(&mut Self) -> bool)]
    #[flux_rs::no_panic_if(Self::next_no_panic())]
    fn next(&mut self) -> bool {
        true
    }
}

// Because Flux doesn't support lifetimes inside expressions, I'm running into an ICE
// when I try to e.g. write `no_panic_if` specs for `Iter<'a, u8>`.

// Here's Claude's hypothesis:
// The elided lifetime on `MyIter<u8>` is the trigger: Flux creates ReVar(?0) for `'a`
// then panics in replace_holes when it can't find it in holes.regions.
#[flux_rs::sig(fn(_) -> bool)]
#[flux_rs::no_panic_if(<MyIter<u8> as MyIterator>::next_no_panic())]
pub fn foo(_x: u8) -> bool {
    true
}
