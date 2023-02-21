#![feature(register_tool)]
#![register_tool(flux)]

#[flux::alias(type Nat() = i32{v: 0 <= v})]
type _Nat = i32;

// #[flux::sig(fn(c: Option<bool>) -> Option<Nat>)]
// pub fn test1(c: Option<bool>) -> Option<i32> {
//     let mut x = 10;
//     let mut y = true;
//     c.map(|b| {
//         if b {
//             x += 1;
//             x
//         } else {
//             y = false;
//             20
//         }
//     })
// }

// #[flux::sig(fn(c: Option<bool>) -> Option<i32>)]
// pub fn test0(c: Option<bool>) -> Option<i32> {
//     let x = 1;
//     let y = 2;
//     c.map(|b| if b { x + 1 } else { y + 2 })
// }

#[flux::sig(fn(c: Option<bool>) -> Option<i32>)]
pub fn test0(c: Option<bool>) -> Option<i32> {
    c.map(|b| if b { 1 } else { 2 })
}
