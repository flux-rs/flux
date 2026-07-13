//@compile-flags: -Fsmt-define-fun=true

flux_rs::defs! {
    fn valid(v: int) -> bool {
        v < u32::MAX
    }
}

#[flux_rs::spec(fn(u64[@v]) -> bool[valid(v)])]
fn test(v: u64) -> bool {
    false
    //~^ ERROR refinement type error
}
