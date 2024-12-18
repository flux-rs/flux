#[flux::opts(check_overflow = true)]
mod my_mod {
    const MAX: u32 = std::u32::MAX;

    #[flux::sig(fn(u32[@x], u32[@y]) -> u32[x + y] requires x + y <= MAX)]
    fn add(x: u32, y: u32) -> u32 {
        x + y
    }

    #[flux::sig(fn(u32[@x]) -> u32[x + 2] requires x + 2 <= MAX)]
    fn add2(x: u32) -> u32 {
        x + 2
    }
}
