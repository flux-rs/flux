#[flux::opaque]
#[flux::refined_by(len: int, hrn inv: (int, T) -> bool)]
pub struct IVec<T> {
    inner: Vec<T>,
}

#[flux::trusted]
impl<T> IVec<T> {
    #[flux::spec(fn[hrn inv: (int, T) -> bool] () -> IVec<T>[0, |idx, val| inv(idx, val)])]
    pub fn new() -> IVec<T> {
        Self { inner: vec![] }
    }
}

#[flux::spec(fn () -> IVec<usize>[0, |idx, val| idx < val])]
fn test() -> IVec<usize> {
    IVec::new()
}
