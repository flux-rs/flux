#[flux::sig(fn (head: [i32; _]))]
pub fn test2<const N: usize>(_head: [i32; N]) {}
