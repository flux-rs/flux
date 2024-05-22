pub fn from_array<const N: usize>(items: [i32; N]) -> Vec<i32> {
    items.to_vec()
}

fn test() -> Vec<i32> {
    from_array([1, 2, 3])
}


fn bad<const N:usize>(arr: &[i32; N]) -> i32 {
  arr[0] //~ ERROR refinement type
}

fn good<const N:usize>(arr: &[i32; N]) -> i32 {
    if (N > 0) {
      arr[0] //~ ERROR refinement type
    } else {
        99
    }
}
