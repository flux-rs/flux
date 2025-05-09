// #[flux::sig(fn (i32[@noob]) -> i32[noob+1])]
// pub fn inc(n: i32) -> i32 {
//     n + 1
// }

// #[flux::refined_by(frog:int)]
// pub enum Boogle {
//     #[flux::variant({usize[@noob]} -> Boogle[noob])]
//     MkBoogle(usize),
// }

// #[flux::trusted]
// #[flux::sig(fn (f: F) -> i32[100]
//             where F: FnOnce(i32[@king]) -> i32[king+1])]
// pub fn test0<F>(f: F) -> i32
// where
//     F: FnOnce(i32) -> i32,
// {
//     f(99)
// }

// #[flux::sig(fn () -> i32[100])]
// pub fn client0() -> i32 {
//     test0(|z| z + 1)
// }

// #[flux::sig(fn (i32[@kang]) -> i32[kang+1])]
pub fn bloah(n: i32) -> i32 {
    n + 1
}

pub fn test() {
    bloah(1);
}

// #[flux::sig(fn (f: Frog) -> i32[100]
//             where Frog: FnOnce(i32[@kong]) -> i32[kong+2])]
// pub fn client1<Frog>(f: Frog) -> i32
// where
//     Frog: FnOnce(i32) -> i32,
// {
//     test0(f)
// }
