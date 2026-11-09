type R<T> = Result<T, ()>;
type P<T> = (T, T);
type O<T> = Option<R<T>>;

// Argument substituted inside an ADT's generic argument.
#[flux::sig(fn(cap: u32) -> R<u32{v: v <= cap}>)]
pub fn test00(cap: u32) -> R<u32> {
    Ok(cap)
}

// Argument substituted where `T` is used directly as a type.
#[flux::sig(fn(x: i32) -> P<i32{v: v <= x}>)]
pub fn test01(x: i32) -> P<i32> {
    (x, x)
}

// Nested aliases.
#[flux::sig(fn(x: i32) -> O<i32{v: v <= x}>)]
pub fn test02(x: i32) -> O<i32> {
    Some(Ok(x))
}

// Alias in a struct field mentioning the struct's index.
#[flux::refined_by(n: int)]
pub struct S {
    #[flux::field(i32[n])]
    a: i32,
    #[flux::field(R<i32{v: v <= n}>)]
    b: R<i32>,
}

pub fn test03(s: S) {
    if let Ok(y) = s.b {
        assert(y <= s.a);
    }
}

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}
