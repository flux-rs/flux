#[flux::sig(fn(x: i322) -> bool )] //~ ERROR cannot find type `i322` in this scope
pub fn boo(x: i32) -> bool {
    x > 0
}
