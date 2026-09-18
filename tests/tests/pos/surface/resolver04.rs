// Test that we support `super` in name resolution

struct S;

mod a {
    use super::*;

    #[flux_attrs::spec(fn(S))]
    fn foo(s: S) {}
}

mod b {
    #[flux_attrs::spec(fn(super::S))]
    fn foo(s: super::S) {}
}
