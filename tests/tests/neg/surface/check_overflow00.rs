#[flux::opts(check_overflow = "strict")]
fn add(x: u32, y: u32) -> u32 {
    x + y //~ ERROR arithmetic operation may overflow
}
