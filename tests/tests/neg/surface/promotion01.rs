extern crate flux_core;

#[flux_rs::reflect]
#[derive(PartialEq, Eq)]
enum Gib {
    Foo,
    Bar,
}
flux_core::eq!(Gib);

#[flux_rs::trusted]
#[flux_rs::sig(fn(&Gib[@a], &Gib[@b]) -> bool[a == b])]
fn my_eq(a: &Gib, b: &Gib) -> bool {
    a == b
}

#[flux_rs::sig(fn () -> bool[true])]
pub fn test_foo_eq() -> bool {
    my_eq(&Gib::Foo, &Gib::Foo)
}

#[flux_rs::sig(fn () -> bool[false])]
pub fn test_bar_eq() -> bool {
    my_eq(&Gib::Bar, &Gib::Bar) //~ ERROR refinement type
}

#[flux_rs::sig(fn () -> bool[false])]
pub fn test_neg() -> bool {
    my_eq(&Gib::Foo, &Gib::Foo) //~ ERROR refinement type
}
