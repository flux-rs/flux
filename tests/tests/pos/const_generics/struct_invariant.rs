#[flux::invariant(N > 0)]
pub struct MPU<const N: usize> {
    #[flux::field({ i32 | N > 0 })]
    field: i32,
}

pub fn foo<const N: usize>(x: usize, _mpu: MPU<N>) {
    let _x = x % N;
}

#[flux::invariant(N > 0)]
pub struct MPUGOOD<const N: usize> {
    field: i32,
}

pub fn bar<const N: usize>(x: usize, _mpu: MPUGOOD<N>) {
    let _x = x % N;
}

pub fn baz<const N: usize>() -> i32 {
    if N > 0 {
        let mpu = MPUGOOD::<N> { field: 12 };
        mpu.field
    } else {
        0
    }
}
