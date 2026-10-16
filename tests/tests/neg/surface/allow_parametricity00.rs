fn foo<T>(x: T) -> T {
    x
}

#[flux::sig(fn(i32{v: v > 0}) -> i32{v: v > 0})]
pub fn test00(x: i32) -> i32 {
    foo(x) //~ ERROR refinement type
}

#[flux::opts(allow_parametricity)]
mod m {
    #[flux::opts(allow_parametricity = false)]
    #[flux::sig(fn(i32{v: v > 0}) -> i32{v: v > 0})]
    pub fn test01(x: i32) -> i32 {
        super::foo(x) //~ ERROR refinement type
    }
}
