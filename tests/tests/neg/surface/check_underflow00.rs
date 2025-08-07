#[flux::opts(check_overflow = "none")]
pub fn underflow_none(n: u32) -> u32 {
    n - 1 //~ ERROR arithmetic operation may underflow
}

#[flux::opts(check_overflow = "strict-under")]
pub fn underflow_strict_under(n: u32) -> u32 {
    n - 1 //~ ERROR arithmetic operation may underflow
}

#[flux::opts(check_overflow = "strict")]
pub fn underflow_strict(n: u32) -> u32 {
    n - 1 //~ ERROR arithmetic operation may overflow
}

#[flux::opts(check_overflow = "lazy")]
pub fn underflow_lazy(n: u32) -> u32 {
    n - 1
}
