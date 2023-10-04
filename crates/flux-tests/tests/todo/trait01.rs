

// #[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn(it: I) where I: Iterator<Item = i32{v:10<=v}>)]
pub fn foo<I>(it: I)
where
    I: Iterator<Item = i32>,
{
    for x in it {
        assert(0 <= x)
    }
}

#[flux::sig(fn(v: Vec<i32{v:70<=v}>))]
pub fn test_ok(v: Vec<i32>) {
    let zig = v.into_iter();
    foo(zig);
}

#[flux::sig(fn(v: Vec<i32{v:7<=v}>))]
pub fn test_err(v: Vec<i32>) {
    let zig = v.into_iter();
    foo(zig); //~ ERROR: refinement type
}
