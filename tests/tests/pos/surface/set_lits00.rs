// A port from https://drops.dagstuhl.de/storage/00lipics/lipics-vol263-ecoop2023/LIPIcs.ECOOP.2023.17/LIPIcs.ECOOP.2023.17.pdf

use std::collections::HashMap;

use flux_rs::{attrs::*, detached_spec};

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

