#[flux::no_panic]
fn calls_unsafe() {
    wildcard(); //~ ERROR may panic

}

fn wildcard() {
    let x = 32;
}
