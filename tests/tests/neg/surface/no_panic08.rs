#[flux::sig(fn[hrn p: int -> bool](x: i32[@n]) -> bool)]
#[flux_rs::no_panic_if(true || p(n))] //~ ERROR illegal use of refinement parameter
fn foo(x: i32) -> bool {
    true
}
