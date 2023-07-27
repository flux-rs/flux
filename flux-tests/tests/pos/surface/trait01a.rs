#![feature(register_tool)]
#![register_tool(flux)]

use std::vec::IntoIter;

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

// TODO: see todo/trait02.rs
// #[flux::sig(fn(it: IntoIter<i32{v:100<=v}>))]
// pub fn goo<I>(it: IntoIter<i32>) {
//     // fn next<J><J:Iterator) -> Option<J::Item>
//     //  query: what is J::Item when J is IntoIter<Nat>
//     for x in it {
//         assert(10 <= x)
//     }
// }

#[flux::sig(fn(it: I) where I: Iterator<Item = i32{v:0<=v}>)]
pub fn foo<I>(it: I)
where
    I: Iterator<Item = i32>,
{
    for x in it {
        assert(0 <= x)
    }
}
