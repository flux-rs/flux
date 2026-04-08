extern crate flux_core;

fn will_panic(x: u32) -> u32 {
    panic!("ahh!!");
    3
}

#[flux_rs::sig(fn())]
#[flux_rs::no_panic_if(true)]
fn foo() {
    let opt: Option<u32> = Option::None;
    opt.map(|x| will_panic(x)); //~ ERROR: may panic

    opt.map_or(42, |x| {
        will_panic(3) //~ ERROR: may panic
    });

    opt.inspect(|x| {
        will_panic(3); //~ ERROR: may panic
    });
}
