//! Check we normalize function signature on entry
#![allow(dead_code)]

trait MyTrait {
    type A;
}

impl MyTrait for i32 {
    type A = i32;
}

fn test<T>(x: <T as MyTrait>::A) -> i32
where
    T: MyTrait<A = i32>,
{
    x + 1
}
