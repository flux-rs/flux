// test that we correctly parse annotations expanded from a macro

macro_rules! make_assert {
    ($a:literal) => {
        #[flux_rs::sig(fn(bool[$a]))]
        fn assert(_: bool) {
            let x = $a;
        }
    };
}

make_assert!(true);

#[flux_rs::should_fail]
fn test00() {
    assert(0 > 1);
}
