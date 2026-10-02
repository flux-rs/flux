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
  )]

#[flux::spec(fn() -> i32{v:pos(v)})]
fn test_fail() -> i32 {
    2 - 9 //~ ERROR refinement type
}
