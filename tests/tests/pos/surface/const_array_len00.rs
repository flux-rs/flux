#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn(&[T; N]) -> usize[N])]
#[flux::trusted]
pub fn my_size<T, const N: usize>(arr: &[T; N]) -> usize {
    arr.len()
}

pub fn test1() {
    let arr0: [i32; 5] = [10, 20, 30, 40, 50];
    assert(my_size(&arr0) == 5);
}
