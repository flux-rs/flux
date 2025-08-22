#![feature(never_type)]

pub trait Foo {
    fn foo(_b: !);
}

impl Foo for bool {
    fn foo(_b: !) {}
}
