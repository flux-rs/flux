// Error on both of these as they may overflow
#![flux::opts(check_overflow = "strict")]
mod my_mod {
    fn add(x: u32, y: u32) -> u32 {
        x + y //~ ERROR arithmetic operation may overflow
    }

    fn add2(x: u32) -> u32 {
        x + 2 //~ ERROR arithmetic operation may overflow
    }
}
