
#[flux::sig(fn () -> usize[11])]
fn test() -> usize {
    let [x, y] = [1, 10];
    x + y
}
