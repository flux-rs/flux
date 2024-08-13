struct S<T> {
    f: T,
}

fn test00<T>(x: S<T>, y: S<T>) -> S<T>
where
    S<T>: std::ops::Mul<Output = S<T>>,
{
    x * y
}
