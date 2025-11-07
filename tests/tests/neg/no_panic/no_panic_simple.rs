#[flux::no_panic]
fn calls_unsafe() {
    wildcard(); // ~ ERROR call to function that may panic
}

fn wildcard() {
    let x = 32;
}
