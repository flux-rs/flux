// tests set literals #{ e1, e2, ..., en }

use flux_rs::{assert, attrs::*};

#[reflect]
enum ExprLbl {
    Var,
    Cst,
    Not,
    Or,
    And,
    Xor,
}

#[opaque]
#[refined_by(s: Set<int>)]
struct Foo;

#[trusted]
#[spec(fn() -> Foo[#{ 1, 2, 3 }])]
fn foo() -> Foo {
    Foo
}

#[trusted]
#[spec(fn(&Foo[@f], n:i32) -> bool[set_is_in(n, f)])]
fn foo_mem(f: &Foo, n: i32) -> bool {
    todo!()
}

#[opaque]
#[refined_by(s: Set<ExprLbl>)]
struct Bar;

#[trusted]
#[spec(fn() -> Bar[#{ ExprLbl::Var, ExprLbl::Cst }])]
fn bar() -> Bar {
    Bar
}

fn test() {
    let f = foo(); // Foo[#{ 1, 2, 3 }]
    assert(foo_mem(&f, 1));
    assert(foo_mem(&f, 2));
    assert(foo_mem(&f, 3));
    assert(!foo_mem(&f, 4));
}
