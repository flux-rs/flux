#[flux::generics(Self as base)]
trait SelfAsBase {}

// Check we report error during conv in a trusted function
#[flux::trusted]
fn test_get<T>()
where
    T: SelfAsBase, //~ ERROR values of this type cannot be used as base sorted instances
{
}
