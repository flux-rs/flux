#[flux_rs::refined_by(m: Map<int, int>)]
#[flux_rs::opaque]
pub struct S1<const N: usize> {
    _arr: [usize; N],
}

const MY_N: usize = 10;

#[flux_rs::refined_by(gloop: S1)]
pub struct S2 {
    #[field(S1<_>[gloop])]
    pub s1: S1<MY_N>,
}

#[flux_rs::refined_by(zoo: S1)]
pub struct S3<const M: usize> {
    #[field(S1<_>[zoo])]
    pub s1: S1<M>,
}
