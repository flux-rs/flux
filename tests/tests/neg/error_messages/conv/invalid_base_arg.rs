#[flux::generics(Self as base)]
trait SelfAsBase {}

fn test00<T>()
where
    T: SelfAsBase, //~ ERROR values of this type cannot be used as base sorted instances
{
}

#[flux::generics(T as base)]
trait TAsBase<T> {}

fn test01<T>()
where
    i32: TAsBase<T>, //~ ERROR values of this type cannot be used as base sorted instances
{
}
