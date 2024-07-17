struct MPU<const N: usize> {
    #[flux::field({ i32 | N > 0 })]
    field: i32,
}

// MPU is missing a struct invariant such that we always know `N > 0`
fn foo<const N: usize>(x: usize, mpu: MPU<N>) {
    let x = x % N; //~ ERROR assertion might fail
}
