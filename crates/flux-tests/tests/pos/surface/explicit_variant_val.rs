fn max<T: Ord>(a: T, b: T) -> T {
    match a.cmp(&b) {
        std::cmp::Ordering::Less => a,
        std::cmp::Ordering::Equal => a,
        std::cmp::Ordering::Greater => b,
    }
}
