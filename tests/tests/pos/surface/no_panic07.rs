#[flux_rs::no_panic_if(n != 0)]
#[flux_rs::sig(fn (x: i32[@n]) -> i32[9])]
fn foo(x: i32) -> i32 {
    if x == 0 {
        panic!("AHH!");
    }
    9
}

#[flux_rs::no_panic]
fn bar() {
    foo(1); // a okay. :)
}
