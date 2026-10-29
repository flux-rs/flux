//@run-rustfix
//@normalize-stderr-test: "(?s).*" -> ""
//@rustfix-only-machine-applicable
//@compile-flags: -Fsuggestions=true -Ffix-suggestions
// The replacement must not resolve Vec to shadow::Vec.
#![flux::opts(check_overflow = "strict")]

mod shadow {
    pub struct Vec<T>(pub T);
}

mod target {
    use crate::shadow::Vec;

    #[flux::sig(fn(std::vec::Vec<u32>, u32) -> u32)]
    pub fn checked(xs: std::vec::Vec<u32>, n: u32) -> u32 {
        let _ = xs;
        n + 1
    }
}
