#[flux::no_panic]
fn calls_unsafe() {
    wildcard(); //~ ERROR 3:5: 3:15: call to function that may panic

}

fn wildcard() {
    let x = 32;
}
