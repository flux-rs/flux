#![flux::defs {
    fn foo(n:int) -> bool;
    fn bar(n:int) -> bool { foo(n) }
}]

#[flux::trusted]
#[flux::sig(fn(n:i32) -> bool[foo(n)])]
fn is_foo(n: i32) -> bool {
    n > 10
}

#[flux::sig(fn(n:i32) -> bool[bar(n)])]
fn is_bar(n: i32) -> bool {
    is_foo(n)
}
