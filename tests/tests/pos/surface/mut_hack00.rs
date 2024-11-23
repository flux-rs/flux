#[flux::sig(fn (xs: &mut { [i32][@n] | n > 1}))]
fn lib1(_xs: &mut [i32]) {}

#[flux::sig(fn (xs: {&mut [i32][@n] | n > 1}))]
fn lib2(_xs: &mut [i32]) {}

#[flux::sig(fn () -> &mut [i32][10])]
fn boo() -> &'static mut [i32] {
    todo!()
}

fn test() {
    let ys = boo();
    lib2(ys);
    lib1(ys);
}
