// `allow_parametricity` on a function, an impl, and a module

fn foo<T>(x: T) -> T {
    x
}

#[flux::opts(allow_parametricity)]
#[flux::sig(fn[hrn q: T -> bool](T{v:q(v)}) -> T{v: q(v)})]
pub fn test00<T>(x: T) -> T {
    foo(x)
}

#[flux::opts(allow_parametricity = true)]
#[flux::sig(fn(i32{v: v > 0}) -> i32{v: v > 0})]
pub fn test01(x: i32) -> i32 {
    foo(x)
}

pub struct S;

#[flux::opts(allow_parametricity)]
impl S {
    #[flux::sig(fn(&S, i32{v: v > 0}) -> i32{v: v > 0})]
    pub fn test02(&self, x: i32) -> i32 {
        foo(x)
    }
}

#[flux::opts(allow_parametricity)]
mod m {
    #[flux::sig(fn(i32{v: v > 0}) -> i32{v: v > 0})]
    pub fn test03(x: i32) -> i32 {
        super::foo(x)
    }
}
