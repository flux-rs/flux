#[flux::no_panic]
fn calls_safe() {
    foo();

}

#[flux::no_panic]
fn foo() -> i32{
    42
}
