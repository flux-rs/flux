#[flux::sig(fn (head: [i32; N]))]
fn test1<const N: usize>(head: [i32; N]) {}

#[flux::sig(fn (head: [i32; _]))]
fn test2<const N: usize>(head: [i32; N]) {}
