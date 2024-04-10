#[flux::sig(fn(&[i32{v : v > 0}]) -> &[i32{v : v >= 0}])]
fn first_half(slice: &[i32]) -> &[i32] {
    let mid = slice.len() / 2;
    let (fst, snd) = slice.split_at(mid);
    fst
}

#[flux::sig(fn(&[i32{v : v > 0}]) -> Option<&i32{v : v >= 0}>)]
fn first(slice: &[i32]) -> Option<&i32> {
    slice.first()
}

#[flux::sig(fn(&mut [i32{v : v > 0}]))]
fn inc_fst(slice: &mut [i32]) {
    if let Some(x) = slice.first_mut() {
        *x += 1;
    }
}
