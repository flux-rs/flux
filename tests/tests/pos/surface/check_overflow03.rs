const MAX: u32 = std::u32::MAX;

struct MyStruct {
    inner: u32,
}

#[flux::opts(check_overflow = true)]
trait MyTrait {
    #[flux::sig(fn(u32[@x], { u32[@y] | x + y <= MAX }) -> u32[x + y] )]
    fn add(x: u32, y: u32) -> u32;
}

impl MyTrait for MyStruct {
    #[flux::sig(fn(u32[@x], { u32[@y] | x + y <= MAX }) -> u32[x + y] )]
    fn add(x: u32, y: u32) -> u32 {
        x + y
    }
}
