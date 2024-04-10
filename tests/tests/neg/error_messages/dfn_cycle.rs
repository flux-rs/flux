#![flux::defs {
    fn even(x: int) -> bool { x == 0 || odd(x-1) } //~ ERROR cycle
    fn odd(x: int) -> bool { x == 1 || even(x-1) }
}]

#[flux::sig(fn(x:i32) -> i32[x+1])]
pub fn test(x: i32) -> i32 {
    x + 1
}
