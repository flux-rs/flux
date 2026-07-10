// Test that we support `super` in name resolution

struct S;

mod a {
    use super::*;

    #[flux_rs::spec(fn(S))]
    fn foo(s: S) {}
}

mod b {
    #[flux_rs::spec(fn(super::S))]
    fn foo(s: super::S) {}
}
