// See <https://github.com/flux-rs/flux/issues/1510#issue-3983965907>

use flux_rs::attrs::*;

#[assoc(fn my_assoc(x: int) -> bool)]
trait MyTrait<'a> {}

#[spec(fn(i32{v: T::my_assoc(v)}))]
fn test<T>(f: i32)
where
    for<'a> T: MyTrait<'a>,
{
}
