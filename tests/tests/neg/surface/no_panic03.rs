#[flux::no_panic] //~ ERROR: duplicated attribute
#[flux::no_panic_if(x > 0)]
fn bar() -> i32 {
    3
}
