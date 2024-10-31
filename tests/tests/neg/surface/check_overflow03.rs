struct MyStruct {
    inner: u32,
}

trait MyTrait {
    fn add(x: u32, y: u32) -> u32;
}

#[flux::check_overflow]
impl MyTrait for MyStruct {
    fn add(x: u32, y: u32) -> u32 {
        x + y //~ ERROR arithmetic operation may overflow
    }
}
