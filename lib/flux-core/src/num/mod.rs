
use flux_attrs::*;

#[extern_spec(core::num)]
impl usize {
    #[no_panic]
    fn saturating_sub(self, other: usize) -> usize;

}