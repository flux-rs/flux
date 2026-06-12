#![flux::defs(

    fn lt(x: int, y: int) -> bool {
        x < y
    }

    fn cmp0(x:int, cmp: fn(int, int) -> bool) -> bool {
        cmp(0, x)
    }

    fn pos(n: int) -> bool {
        cmp0(n, lt)
    }

    fn pos_lam(n: int) -> bool {
        cmp0(n, |x, y| x < y)
    }

  )]

#[flux::spec(fn() -> i32{v:pos(v)})]
fn test0() -> i32 {
    29
}

#[flux::spec(fn() -> i32{v:pos_lam(v)})]
fn test1() -> i32 {
    29
}
