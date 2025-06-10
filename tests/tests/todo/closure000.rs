enum Blah {
    MkBlah(i32),
}

pub fn test00<T, F>(f: F) -> T
where
    F: FnOnce(i32) -> T,
{
    f(0)
}

pub fn test01() -> Blah {
    test00(Blah::MkBlah)
}
