#[flux::assoc(fn f(self: Self) -> bool)]
pub trait MyTrait {
    fn method(&self) -> i32;
}

#[flux::assoc(fn f(x: int) -> bool { 1 + x })] //~ ERROR mismatched sorts
impl MyTrait for i32 {
    fn method(&self) -> i32 {
        10
    }
}
