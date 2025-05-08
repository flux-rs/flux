// #[flux::sig(fn (i32[@noob]) -> i32[noob+1])]
// pub fn inc(n: i32) -> i32 {
//     n + 1
// }

// #[flux::refined_by(frog:int)]
// pub enum Boogle {
//     #[flux::variant({usize[@noob]} -> Boogle[noob])]
//     MkBoogle(usize),
// }

#[flux::sig(fn (f: F) -> i32[100]
            where F: FnOnce(i32[@king]) -> i32[king+1])]
pub fn test0<F>(f: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(99)
}
