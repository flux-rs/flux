trait Trait1 {
    type Assoc1;
}

impl Trait1 for i32 {
    type Assoc1 = bool;
}

trait Trait2 {
    type Assoc2;
}

struct S<T> {
    fld: T,
}

impl<T1, T2> Trait2 for S<T2>
where
    T2: Trait1<Assoc1 = T1>,
{
    type Assoc2 = T1;
}

fn test(x: <S<i32> as Trait2>::Assoc2) {}
