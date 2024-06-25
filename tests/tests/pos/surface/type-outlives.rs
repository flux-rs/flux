struct S<'a, T: 'a> {
    x: T,
    y: &'a i32,
}
