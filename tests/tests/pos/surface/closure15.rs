// Test that we can use tuple struct as constructors

struct S(i32);

fn foo(x: impl FnOnce(i32) -> S) {}

fn baz() {
    foo(S)
}
