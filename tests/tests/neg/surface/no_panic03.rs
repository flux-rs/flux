#[flux::no_panic] //~ ERROR: duplicated attribute
#[flux::no_panic_if(x > 0)]
#[flux::sig(fn() -> i32)]
fn bar() -> i32 {
    3
}
