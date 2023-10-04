#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn(it: I) where I: Iterator<Item = i32{v:0<=v}>)]
pub fn foo<I>(it: I)
where
    I: Iterator<Item = i32>,
{
    for x in it {
        assert(0 <= x)
    }
}

pub fn test1() {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    foo(v.into_iter());
}

#[flux::sig(fn(v: Vec<i32{v:70<=v}>))]
pub fn test_ok(v: Vec<i32>) {
    let zig = v.into_iter();
    foo(zig);
}
