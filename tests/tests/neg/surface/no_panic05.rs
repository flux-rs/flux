#[flux::no_panic] //~ ERROR: duplicated attribute
#[flux::no_panic_if(true)]
fn my_fn() -> i32 {
    3
}
