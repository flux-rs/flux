#[flux::sig(fn(b:bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn (xink: i32, it: Igloo) where Igloo: Iterator<Item = i32{v: xink < v}>)]
pub fn foo<Igloo>(x: i32, mut it: Igloo)
where
    Igloo: Iterator<Item = i32>,
{
    if let Some(val) = it.next() {
        assert(x < val)
    }
}

// pub fn baz() {
//     foo(1, Some(2).into_iter())
// }
