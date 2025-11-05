use flux_rs::attrs::*;

#[spec(fn (&[usize;_]) -> usize requires N > 0)]
pub fn test<const N: usize>(chunk: &[usize; N]) -> usize {
    chunk[0]
}

pub fn call_test() {
    let arr_ok = [1, 2, 3];
    let _x = test::<3>(&arr_ok);

    let arr_bad = [];
    let _x = test::<0>(&arr_bad); //~ ERROR refinement type
}
