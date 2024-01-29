#[flux::sig(fn(x: i322) -> bool )] //~ ERROR cannot resolve
pub fn boo(x: i32) -> bool {
    x > 0
}
