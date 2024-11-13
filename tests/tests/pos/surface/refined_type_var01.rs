fn foo<T>(x: T) -> T {
    x
}

#[flux::sig(fn[hrn q: T -> bool](T{v:q(v)}) -> T{v: q(v)})]
pub fn baz<T>(x: T) -> T {
    foo(x)
}
