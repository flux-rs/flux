#[flux::sig(fn(x: Option<usize{v: check == v => v > 0}>, check: usize) -> Option<usize{v: v > 0}>)]
fn test00(x: Option<usize>, check: usize) -> Option<usize> {
    match x {
        Some(i) if i == check => Some(i),
        _ => None,
    }
}
