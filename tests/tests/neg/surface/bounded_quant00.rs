#![flux::defs {
    fn magic(xing:int, yonk:int) -> bool;

    fn magic_all(noob:int) -> bool {
        forall i in 0 .. 4 {
            magic(i, noob)
        }
    }

    fn magic_ex(n:int) -> bool {
        exists i in 0 .. 4 {
            i == n
        }
    }
}]

#[flux::trusted]
#[flux::sig(fn(x:i32, y:i32) ensures magic(x, y))]
pub fn do_magic(_x: i32, _y: i32) {}

// forall tests ----------------------------------------------------------------

#[flux::sig(fn({i32[@n] | magic_all(n)}) ensures magic(4, n))]
pub fn test_all_l(_x: i32) {} //~ ERROR refinement type

#[flux::sig(fn(n:i32) ensures magic_all(n))]
pub fn test_all_r(n: i32) {
    //~^ ERROR refinement type
    do_magic(0, n);
    do_magic(1, n);
    do_magic(3, n);
}

// exists tests ----------------------------------------------------------------
#[flux::sig(fn({i32[@n] | magic_ex(n)}) -> bool[true])]
pub fn test_exi_l(n: i32) -> bool {
    n == 0 || n == 1 || n == 3 //~ ERROR refinement type
}

#[flux::sig(fn(n:i32) -> bool[magic_ex(n)])]
pub fn test_exi_r(n: i32) -> bool {
    n == 0 || n == 2 || n == 3 //~ ERROR refinement type
}
