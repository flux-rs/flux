#![flux::defs {
    fn magic(x:int, y:int) -> bool;

    fn magic_all(n:int) -> bool {
        forall i in 0 .. 4 {
            magic(i, n)
        }
    }

}]

#[flux::trusted]
#[flux::sig(fn(x:i32, y:i32) ensures magic(x, y))]
fn do_magic(_x: i32, _y: i32) {}

// forall tests ----------------------------------------------------------------

#[flux::sig(fn({i32[@n] | magic_all(n)}) ensures magic(3, n))]
pub fn test_all_l(_x: i32) {}

#[flux::sig(fn(n:i32) ensures magic_all(n))]
pub fn test_all_r(n: i32) {
    do_magic(0, n);
    do_magic(1, n);
    do_magic(2, n);
    do_magic(3, n);
}
