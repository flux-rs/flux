#[flux_rs::no_panic_if(true)]
fn foo1() {
    evil(); //~ ERROR may panic
    let x = || {
        evil(); //~ ERROR may panic
    };
}

#[flux_rs::no_panic]
fn foo2() {
    evil(); //~ ERROR may panic
    let x = || {
        evil(); //~ ERROR may panic
    };
}

fn evil() {
    panic!("yoohoo!");
}
