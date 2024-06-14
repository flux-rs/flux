pub fn test01<const N: usize>(arr: &[i32; N]) -> i32 {
    arr[0] //~ ERROR refinement type
}

// fn test02<const N: usize>(arr: &[i32; N]) -> i32 {
//     if (N > 0) {
//         arr[0]
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
