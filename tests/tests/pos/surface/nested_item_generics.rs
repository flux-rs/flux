// An item nested in a generic item can use its own generic parameters, even if they shadow the
// ones of the enclosing item

use flux_attrs::*;

pub fn outer<T>(x: T) -> T {
    #[spec(fn(x: T) -> T)]
    fn inner<T>(x: T) -> T {
        x
    }

    inner(x)
}
