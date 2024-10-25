const MAX: u32 = std::u32::MAX;

struct MyStruct {
    inner: u32
}

#[flux::check_overflow]
trait MyTrait {
    fn add(x: u32, y: u32) -> u32;
}

impl MyTrait for MyStruct {
    #[flux::sig(fn(u32[@x], u32[@y]) -> u32[x + y] requires x + y <= MAX)]
    fn add(x: u32, y: u32) -> u32 {
        x + y
    }
}
