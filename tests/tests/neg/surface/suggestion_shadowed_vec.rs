// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 1
// suggestion: ::vec::Vec<u32>
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
        n + 1 //~ ERROR arithmetic operation may overflow
    }
}
