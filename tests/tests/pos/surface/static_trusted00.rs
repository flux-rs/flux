//! A trusted static's spec is assumed without checking its initializer.

#[flux::trusted(reason = "test")]
#[flux::spec(u32[1])]
static ONE: u32 = 2;

#[flux::sig(fn() -> u32[1])]
pub fn one() -> u32 {
    ONE
}
