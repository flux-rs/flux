// pub fn test000<const N: usize>() -> i32 {
//     0
// }

// pub fn test00_client() {
//     test000::<3>();
// }

// pub fn test001<const N: usize>() -> usize {
//     N
// }

#[flux::sig(fn(x:A) -> usize[N+2])]
pub fn test002<A, const N: usize>(_x: A) -> usize {
    N + 2
}

#[flux::sig(fn() -> usize[5])]
pub fn test002_client() -> usize {
    test002::<bool, 3>(true)
}

#[flux::sig(fn(x:A) -> usize{v:N < v})]
pub fn test003<A, const N: usize>(_x: A) -> usize {
    N + 2
}

#[flux::sig(fn(&i32) -> usize{v: 10 < v})]
pub fn test004<const N: usize>(_zink: &i32) -> usize {
    if 10 < N {
        N
    } else {
        15
    }
}

// pub fn test01<const N: usize>(arr: &[i32; N]) -> i32 {
//     arr[0] //~ ERROR refinement type
// }

// fn test02<const N: usize>(arr: &[i32; N]) -> i32 {
//     if (N > 0) {
//         arr[0] //~ ERROR refinement type
//     } else {
//         99
//     }
// }

// pub fn from_array<const N: usize>(items: [i32; N]) -> Vec<i32> {
//     items.to_vec()
// }

// fn test03() -> Vec<i32> {
//     from_array([1, 2, 3])
// }
