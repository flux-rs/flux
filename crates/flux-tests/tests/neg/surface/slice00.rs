#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(&mut [i32{v : v > 0}]) -> &mut [i32{v : v >= 0}])]
fn first_half(slice: &mut [i32]) -> &mut [i32] {
    let mid = slice.len() / 2;
    let (fst, snd) = slice.split_at_mut(mid); //~ ERROR refinement type
    fst
}

#[flux::sig(fn(&[i32{v : v >= 0}]) -> Option<&i32{v : v > 0}>)]
fn first(slice: &[i32]) -> Option<&i32> {
    slice.first() //~ ERROR refinement type
}

#[flux::sig(fn(&mut [i32{v : v > 0}]))]
fn inc_fst(slice: &mut [i32]) {
    if let Some(x) = slice.first_mut() {
        //~^ ERROR refinement type
        *x -= 1;
    }
}
