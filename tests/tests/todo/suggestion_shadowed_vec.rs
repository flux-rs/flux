#![flux::opts(check_overflow = "strict")]

mod shadow {
    pub struct Vec<T>(pub T);
}

mod target {
    use crate::shadow::Vec;

    #[flux::sig(fn(Vec<u32>, u32[@n]) -> u32 requires n + 1 <= 4294967295)]
    pub fn checked(xs: std::vec::Vec<u32>, n: u32) -> u32 {
        let _ = xs;
        n + 1
    }
}
