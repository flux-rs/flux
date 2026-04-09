#[flux::no_panic] //~ ERROR: duplicated attribute
#[flux::no_panic_if(true)]
#[flux::sig(fn() -> i32)]
fn my_fn() -> i32 {
    3
}
