// test that we correctly parse annotations expanded from a macro
use flux_attrs::*;

macro_rules! make_assert {
    ($a:literal) => {
        #[spec(fn(bool[$a]))]
        fn assert(_: bool) {
            let x = $a;
        }
    };
}

make_assert!(true);

#[should_fail]
fn test00() {
    assert(0 > 1);
}
