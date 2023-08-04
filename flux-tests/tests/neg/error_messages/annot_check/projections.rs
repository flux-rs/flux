#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn(it: I) where I: Iterator<Item = i32{v:0+v}>)] //~ ERROR mismatched sorts
pub fn foo<I>(it: I)
where
    I: Iterator<Item = i32>,
{
    for x in it {
        assert(0 <= x)
    }
}

// #[flux::sig(fn () -> i32{v:1+v})]
// fn zog() -> i32 {
//     0
// }

#[flux::sig(fn () -> impl Iterator<Item = i32{v:1+v}>)] //~ ERROR mismatched sorts
pub fn test_pass() -> impl Iterator<Item = i32> {
    Some(10).into_iter()
}
