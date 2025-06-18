use flux_rs::attrs::*;

#[trusted]
#[spec(fn (&[_][@n]) -> usize[n])]
fn len<T>(z: &[T]) -> usize {
    z.len()
}

// This tests the `unfold` done for FakeForPtrMetadata reads
// mut-ref-unfolding problem: adding the below spec makes this test pass; sure would be nice to
// have it work "out of the box"
// #[spec(fn (d: &mut [i32]) ensures d: [i32])]
pub fn blah(d: &mut [i32]) {
    if len(d) > 0 {
        d[0] = 10; //~ ERROR assertion might fail
    }
}
