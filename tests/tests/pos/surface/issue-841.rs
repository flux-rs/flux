enum E {
    A,
    B,
}

fn test00(items: &[i32]) -> i32 {
    for i in items {
        if matches!(E::A, E::B) {};
    }
    0
}
