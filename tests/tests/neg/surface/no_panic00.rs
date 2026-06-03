#[flux::no_panic]
fn calls_unsafe() {
    wildcard(); //~ ERROR may panic
}

fn wildcard() {
    let x = 32;
    wildcard2(); // calling a function that may panic
}

fn wildcard2() {
    let x = 32;
    println!("hello worlddd");
}
