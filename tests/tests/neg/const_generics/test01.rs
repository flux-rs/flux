pub fn test01<const N: usize>(arr: &[i32; N]) -> i32 {
    arr[0] //~ ERROR assertion might fail
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

struct Bloop<const N: usize>([i32; N]);

impl<const M: usize> Bloop<M> {
    fn test_array_good(&self) -> i32 {
        if (M > 0) {
            self.0[0]
        } else {
            99
        }
    }

    fn test_array_bad(&self) -> i32 {
        self.0[0] //~ ERROR assertion might fail
    }
}
