#![feature(register_tool, box_patterns)]
#![register_tool(flux)]

pub struct S<T1, T2, T3 = i32> {
    x: T1,
    y: T2,
    z: T3,
}

#[flux::sig(fn(S) -> ())] //~ ERROR this struct must take 2 generic arguments
pub fn test01(bob: S<i32, i32>) {}

#[flux::sig(fn(S<i32>) -> ())] //~ ERROR this struct must take 2 generic arguments
pub fn test02(bob: S<i32, i32>) {}

#[flux::sig(fn(S<i32, i32, i32, i32>) -> ())] //~ ERROR this struct must take 2 generic arguments
pub fn test03(bob: S<i32, i32>) {}
