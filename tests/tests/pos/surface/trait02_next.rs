#[flux::sig(fn(b:bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn (xink: i32, it: I) where I: Iterator<Item = i32{v: xink < v}>)]
pub fn foo<I>(x: i32, mut it: I)
where
    I: Iterator<Item = i32>,
{
    if let Some(val) = it.next() {
        assert(x < val)
    }
}
