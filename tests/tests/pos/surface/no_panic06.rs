#[flux::no_panic]
fn foo() {
    bar();
}

fn bar() {
    baz();
    qux();
}

fn baz() -> i32 {
    4
}

fn qux() -> i32 {
    3
}
