flux_rs::defs! {
    fn foo(x: int) -> bool;
    qualifier Foo(x: int) {
        foo(x)
    }
}

#[flux::spec(fn(x: usize[@n]) -> usize{ v : v >= 5 })]
fn test(x: usize) -> usize {
    let mut i = x;
    while i < 5 {
        i += 1;
    }
    i
}