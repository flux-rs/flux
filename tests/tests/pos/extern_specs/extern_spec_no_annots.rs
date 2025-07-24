// Check that an extern spec without annotations works. This goes through
// lifting. So we want to ensure lifting upholds the extern specs invariants
// the same as desugaring.

use flux_rs::attrs::*;

#[extern_spec(core::ops)]
trait RangeBounds<T> {
    fn contains<U>(&self, item: &U) -> bool
    where
        T: PartialOrd<U>,
        U: ?Sized + PartialOrd<T>;
}
