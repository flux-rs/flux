//! Regression test: an identifier declared and referenced inside the same `macro_rules!`
//! expansion must resolve inside a flux attribute (`#[sig]`), even when it's written as a
//! literal token in the macro body (as opposed to a substituted `$name:ident` metavariable).
#![allow(dead_code)]

use flux_attrs::*;

// Case 1: a type parameter declared in the macro's own `impl<T>` header.
struct Wrapper<T>(T);

macro_rules! wrapper_specs {
    ($m:tt) => {
        impl<T> Wrapper<T> {
            #[sig(fn(x: T) -> T)]
            fn identity(x: T) -> T {
                x
            }
        }
    };
}

wrapper_specs!(dummy);

// Case 2: an ordinary (non-generic) type declared inside the macro body.
macro_rules! make_stuff {
    () => {
        struct Foo;

        #[sig(fn(x: Foo) -> Foo)]
        fn identity_foo(x: Foo) -> Foo {
            x
        }
    };
}

make_stuff!();

// Case 3: a type declared inside a macro, then referenced from a flux attribute *outside* the
// macro entirely (ordinary Rust name resolution finds `S` here regardless of hygiene, since
// items introduced by a macro are visible to the enclosing scope like any other item).
macro_rules! declare_s {
    () => {
        struct S;
    };
}

declare_s!();

#[sig(fn(x: S) -> S)]
fn identity_s(x: S) -> S {
    x
}
