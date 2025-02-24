struct MPU<const N: usize> {
    #[flux::field({ i32 | N > 0 })]
    field: i32,
}

// MPU is missing a struct invariant such that we always know `N > 0`
fn foo<const N: usize>(x: usize, mpu: MPU<N>) {
    let x = x % N; //~ ERROR assertion might fail
}



#[flux::invariant(N > 0)]
pub struct MPUGOOD<const N: usize> {
    field: i32,
}

pub fn bar<const N: usize>(x: usize, _mpu: MPUGOOD<N>) {
    let _x = x % N;
}

pub fn baz<const N: usize>() -> i32 {
  let mpu = MPUGOOD::<N> { field: 12 }; //~ ERROR refinement type
  mpu.field
}

