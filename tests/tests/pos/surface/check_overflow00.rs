const MAX: u32 = std::u32::MAX;

// Error on this as it may overflow
#[flux::check_overflow]
#[flux::sig(fn (u32[@x], u32[@y], u32[@z]) -> u32[x + y + z] requires x + y + z <= MAX)]
fn add_three(x: u32, y: u32, z: u32) -> u32 {
    x + y + z
}
