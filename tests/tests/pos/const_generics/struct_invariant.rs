#[flux::invariant(N > 0)]
struct MPU<const N: usize> {
    #[flux::field({ i32 | N > 0 })]
    field: i32,
}

fn foo<const N: usize>(x: usize, mpu: MPU<N>) {
    let x = x % N;
}
