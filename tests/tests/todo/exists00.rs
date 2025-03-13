#![flux::defs {
    fn magic_ex(n:int) -> bool {
        exists i in 0 .. 4 {i == n}
    }
}]

// exists tests ----------------------------------------------------------------
#[flux::sig(fn(n:{i32 | magic_ex(n)}) -> bool[true])]
pub fn test_exi_l(n: i32) {
    n == 0 || n == 1 || n == 2 || n == 3
}

#[flux::sig(fn(n:i32) -> bool[magic_ex(n)])]
pub fn test_exi_r(n: i32) {
    n == 0 || n == 1 || n == 2 || n == 3
}
