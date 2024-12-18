const MAX: u32 = std::u32::MAX;

#[flux_rs::refined_by(inner: int)]
struct MyStruct {
    #[field(u32[inner])]
    inner: u32,
}

impl MyStruct {
    fn add1(&self) -> u32 {
        self.inner + 1
    }

    // Error as this may overflow
    #[flux::opts(check_overflow = true)]
    #[flux::sig(fn (&MyStruct[@inner]) -> u32[inner + 2] requires inner + 2 <= MAX)]
    fn add2(&self) -> u32 {
        self.inner + 2
    }
}
