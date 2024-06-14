pub fn test01<const N: usize>(arr: &[i32; N]) -> i32 {
    arr[0] //~ ERROR refinement type
}

pub fn test02<const N: usize>(arr: &[i32; N]) -> i32 {
    if N > 0 {
        arr[0]
    } else {
        99
    }
}

#[flux::trusted]
#[flux::sig(fn(items:_) -> usize[N])]
pub fn array_len<const N: usize>(items: &[i32; N]) -> usize {
    items.len()
}

#[flux::sig(fn() -> usize[3])]
fn test03() -> usize {
    array_len(&[1, 2, 3])
}

#[flux::sig(fn() -> usize[3])]
fn test03_bad() -> usize {
    array_len(&[1, 2]) //~ ERROR refinement type
}
