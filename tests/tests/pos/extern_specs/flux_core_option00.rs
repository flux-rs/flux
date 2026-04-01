extern crate flux_core;

#[flux_rs::sig(fn(_) -> _)]
fn will_never_panic(x: u32) -> u32 {
    3
}

#[flux_rs::sig(fn())]
#[flux_rs::no_panic]
fn foo() {
    let opt: Option<u32> = Option::None;
    opt.map(|x| will_never_panic(x));

    opt.map_or(42, |x| will_never_panic(3));

    opt.inspect(|x| {
        will_never_panic(3);
    });
}
