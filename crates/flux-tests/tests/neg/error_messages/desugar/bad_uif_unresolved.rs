#![flux::defs {
    fn foo(x:int, y:int) -> int;
}]

#[flux::sig(fn (i32[fog(10, 20)]) -> i32)] //~ ERROR cannot find function `fog`
pub fn baz(a: i32) -> i32 {
    return a;
}
