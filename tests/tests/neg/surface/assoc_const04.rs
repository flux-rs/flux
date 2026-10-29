// `A::IS_ZST` normalizes to `false`, so the trait's spec demands `10 < v` and
// returning `5` must be rejected. `B::IS_ZST` normalizes to `true`, so the same
// trait spec demands `v == 0` there and returning `0` is fine. A pass on the
// first would mean normalization had made the spec trivially true.

trait Tr {
    const IS_ZST: bool;

    #[flux::spec(fn() -> u32{v: if Self::IS_ZST { v == 0 } else { 10 < v }})]
    fn m() -> u32;
}

struct A;

impl Tr for A {
    const IS_ZST: bool = false;

    #[flux::spec(fn() -> u32[5])]
    fn m() -> u32 {
        //~^ ERROR refinement type
        5
    }
}

struct B;

impl Tr for B {
    const IS_ZST: bool = true;

    #[flux::spec(fn() -> u32[0])]
    fn m() -> u32 {
        0
    }
}
