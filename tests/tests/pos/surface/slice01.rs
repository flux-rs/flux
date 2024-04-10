#[flux::sig(fn(arr: &[i32][@n], i:usize{0 <= i && i < n}) -> i32)]
pub fn foo(arr: &[i32], i: usize) -> i32 {
    arr[i]
}

#[flux::trusted]
#[flux::sig(fn(arr: &[T][@n]) -> usize[n])]
fn len<T>(arr: &[T]) -> usize {
    arr.len()
}

#[flux::sig(fn(arr: &[i32][@n]) -> i32)]
pub fn bar(arr: &[i32]) -> i32 {
    let n = len(arr);
    if 10 < n {
        arr[10]
    } else {
        0
    }
}
