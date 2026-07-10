use flux_rs::*;

#[sig(fn(bool[true]))]
fn assert(_: bool) {}

trait MyTrait {
    type Assoc;

    #[sig(fn(Self::Assoc[@x]) -> Self::Assoc[x])]
    fn f0(x: Self::Assoc) -> Self::Assoc;

    #[sig(fn(x: Self::Assoc) -> Self::Assoc{ v: v == x })]
    fn f1(x: Self::Assoc) -> Self::Assoc;
}

impl MyTrait for () {
    type Assoc = i32;

    #[sig(fn(x: i32) -> i32[x])]
    fn f0(x: i32) -> i32 {
        x
    }

    #[sig(fn(x: i32) -> i32[x])]
    fn f1(x: i32) -> i32 {
        x
    }
}

fn test00() {
    let x = <() as MyTrait>::f0(0);
    assert(x == 0);
}

fn test01() {
    let x = <() as MyTrait>::f1(0);
    assert(x == 0);
}
