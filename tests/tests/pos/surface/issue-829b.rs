trait Trait1 {
    type Assoc1;
}

impl Trait1 for i32 {
    type Assoc1 = i32;
}

trait Trait2 {
    type Assoc2;
}

struct S<T> {
    fld: T,
}

impl<T1, T2, T3> Trait2 for S<T1>
where
    T2: Trait1<Assoc1 = T3>,
    T1: Trait1<Assoc1 = T2>,
{
    type Assoc2 = T1;
}

fn test(x: <S<i32> as Trait2>::Assoc2) {}
