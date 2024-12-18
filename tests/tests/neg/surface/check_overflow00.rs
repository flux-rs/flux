#[flux::opts(check_overflow = true)]
fn add(x: u32, y: u32) -> u32 {
    x + y //~ ERROR arithmetic operation may overflow
}
