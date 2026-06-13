#![flux::defs(
    fn opaque_prop(n: int) -> bool;

    #[hide]
    fn opaque_prop_in_range(lo: int, hi: int) -> bool {
        forall i in int {
            (lo <= i && i < hi) => opaque_prop(i)
        }
    }
)]

#[flux::trusted]
#[flux::spec(fn(lo: usize, hi: usize) ensures opaque_prop_in_range(lo, hi))]
fn assume_opaque_prop(_lo: usize, _hi: usize) {}

#[flux::trusted]
#[flux::spec(fn(n: usize)
    requires opaque_prop_in_range(n, n+1)
    ensures opaque_prop(n)
)]
fn assert_opaque_prop(_n: usize) {}

#[flux::spec(fn() ensures opaque_prop(100))]
pub fn test_ok() {
    assume_opaque_prop(100, 101);
    assert_opaque_prop(100);
}
