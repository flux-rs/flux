// tests set literals #{ e1, e2, ..., en }

use flux_rs::attrs::*;

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

#[opaque]
#[refined_by(s: Set<ExprLbl>)]
struct Bar;

#[trusted]
#[spec(fn() -> Bar[#{ ExprLbl::Var, ExprLbl::Cst }])]
fn bar() -> Bar {
    Bar
}
