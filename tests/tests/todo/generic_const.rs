//-------------------------------------------------------------------------------

pub fn test000<const N: usize>() -> i32 {
    0
}

pub fn test00_client() {
    test000::<3>();
}

pub fn test001<const N: usize>() -> usize {
    N
}

//-------------------------------------------------------------------------------

#[flux::sig(fn(x:A) -> usize[N+2])]
pub fn test002<A, const N: usize>(_x: A) -> usize {
    N + 2
}

#[flux::sig(fn(x:A) -> usize[N+2])]
pub fn test002_bad<A, const N: usize>(_x: A) -> usize {
    N + 1 //~ ERROR refinement type
}

#[flux::sig(fn() -> usize[5])]
pub fn test002_client_a() -> usize {
    test002::<bool, 3>(true)
}

#[flux::sig(fn() -> usize[5])]
pub fn test002_client_a_bad() -> usize {
    test002::<bool, 30>(true) //~ ERROR refinement type
}

#[flux::sig(fn() -> usize[M+2])]
pub fn test002_client_b<const M: usize>() -> usize {
    test002::<bool, M>(true)
}

#[flux::sig(fn() -> usize[M+3])]
pub fn test002_client_b_bad<const M: usize>() -> usize {
    test002::<bool, M>(true) //~ ERROR refinement type
}

//-------------------------------------------------------------------------------

#[flux::sig(fn(x:A) -> usize{v:N < v})]
pub fn test003<A, const N: usize>(_x: A) -> usize {
    N + 2
}

#[flux::sig(fn(x:A) -> usize{v:N < v})]
pub fn test003_bad<A, const N: usize>(_x: A) -> usize {
    N //~ ERROR refinement type
}

#[flux::sig(fn() -> usize{v:3 < v})]
pub fn test003_client_a() -> usize {
    test003::<bool, 3>(true)
}

#[flux::sig(fn() -> usize{v:3 < v})]
pub fn test003_client_a_bad() -> usize {
    test003::<bool, 2>(true) //~ ERROR refinement type
}

#[flux::sig(fn() -> usize{v:M < v})]
pub fn test003_client_b_bad<const M: usize>() -> usize {
    test003::<bool, 2>(true) //~ ERROR refinement type
}

//-------------------------------------------------------------------------------

#[flux::sig(fn() -> usize{v: 10 < v})]
pub fn test004<const N: usize>() -> usize {
    if 10 < N {
        N
    } else {
        15
    }
}

#[flux::sig(fn() -> usize{v: 10 < v})]
pub fn test004_bad<const N: usize>() -> usize {
    if 9 < N {
        N //~ ERROR refinement type
    } else {
        15
    }
}

#[flux::sig(fn() -> usize{v:10 < v})]
pub fn test004_client_a() -> usize {
    test004::<3>()
}

#[flux::sig(fn() -> usize{v:10 < v})]
pub fn test004_client_b<const M: usize>() -> usize {
    test004::<M>()
}

#[flux::sig(fn() -> usize{v:100 < v})]
pub fn test004_client_a_bad() -> usize {
    test004::<3>() //~ ERROR refinement type
}

#[flux::sig(fn() -> usize{v:100 < v})]
pub fn test004_client_b_bad<const M: usize>() -> usize {
    test004::<M>() //~ ERROR refinement type
}

// TODO: Add support for arrays
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
