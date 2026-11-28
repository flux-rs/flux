// `allow_parametricity` on the crate
#![flux::opts(allow_parametricity)]

fn foo<T>(x: T) -> T {
    x
}

#[flux::sig(fn(i32{v: v > 0}) -> i32{v: v > 0})]
pub fn test00(x: i32) -> i32 {
    foo(x)
}
