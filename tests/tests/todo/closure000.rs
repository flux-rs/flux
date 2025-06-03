// #[flux::sig(fn (i32{v: 0 <= v}) -> i32{v: 0 < v})]
// pub fn foo(x: i32) -> i32 {
//     x + 1
// }
//
// // TODO: get `map` working for `Range`
// fn test() -> Vec<i32> {
//     (0..10).map(|i| foo(i)).collect()
// }

// TODO: cannot-match-predicate issue:
// https://github.com/flux-rs/flux/issues/1096
#[flux_rs::sig(fn (f: F) -> i32{v:0 <= v}
               where F: FnMut(&i32{v: 0 <= v}) -> i32{v:0<=v})]
pub fn test00<F>(mut f: F) -> i32
where
    F: FnMut(&i32) -> i32,
{
    let z = 10;
    f(&z)
}

// TODO: cannot-match-predicate issue:
// https://github.com/flux-rs/flux/issues/1096
#[flux_rs::sig(fn (f: F) -> i32[11]
               where F: FnMut(&i32[@k]) -> i32[k+1])]
pub fn test01<F>(mut f: F) -> i32
where
    F: FnMut(&i32) -> i32,
{
    let z = 10;
    f(&z)
}
