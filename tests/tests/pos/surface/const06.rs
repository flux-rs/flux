#[flux::sig(fn (head: [i32; N]))]
pub fn test1<const N: usize>(head: [i32; N]) {}

#[flux::sig(fn (head: [i32; _]))]
pub fn test2<const N: usize>(head: [i32; N]) {}
