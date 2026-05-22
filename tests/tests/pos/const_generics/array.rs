#[flux_rs::trusted]
#[flux_rs::spec(fn (&[T; N]) -> usize[N])]
pub fn my_size<T, const N: usize>(arr: &[T; N]) -> usize {
    arr.len()
}

pub fn test() {
    let arr0: [i32; 5] = [10, 20, 30, 40, 50];
    flux_rs::assert(my_size(&arr0) == 5);
}
