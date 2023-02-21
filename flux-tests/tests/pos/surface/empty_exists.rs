#![feature(register_tool)]
#![register_tool(flux)]

struct S;

fn test00() {
    #[flux::sig(fn(x: S, S{v: v == x}))]
    fn fun(x: S, y: S) {}

    fun(S, S)
}

fn test01() {
    #[flux::sig(fn(x: i32, S{v: x >= 0}))]
    fn fun(x: i32, y: S) {}

    fun(0, S)
}
