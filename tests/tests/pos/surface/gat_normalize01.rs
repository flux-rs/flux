// Normalizing a projection on a GAT with both lifetime and type params through an impl.
// The call to `get_item` returns
//     <Wrapper<bool> as Container>::Item<'r, i32[1]>
// which normalizes through `impl<T> Container for Wrapper<T>` to
//     (&'r bool, i32[1])

use flux_attrs::*;

pub trait Container {
    type Item<'a, U>
    where
        Self: 'a;

    fn item<'a, U>(&'a self, u: U) -> Self::Item<'a, U>;
}

pub struct Wrapper<T> {
    val: T,
}

impl<T> Container for Wrapper<T> {
    type Item<'a, U>
        = (&'a T, U)
    where
        Self: 'a;

    fn item<'a, U>(&'a self, u: U) -> (&'a T, U) {
        (&self.val, u)
    }
}

fn get_item<'a, C: Container, U>(c: &'a C, u: U) -> C::Item<'a, U> {
    c.item(u)
}

#[spec(fn(&Wrapper<bool>) -> i32{v: v > 0})]
pub fn test(w: &Wrapper<bool>) -> i32 {
    let (_, y) = get_item(w, 1);
    y
}
