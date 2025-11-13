use flux_rs::extern_spec;

extern crate flux_core;

#[flux::no_panic]
fn calls_safe() {
    foo();

}

#[flux::no_panic]
fn foo() -> i32{
    let blah = Some(2);
    blah.unwrap();
    2
}
