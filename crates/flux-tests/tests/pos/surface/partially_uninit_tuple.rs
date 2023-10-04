struct S {
    pair: Option<(Vec<i32>, i32)>,
}

fn test(s: &mut S) {
    if let Some((head, tail)) = s.pair.take() {}
}
