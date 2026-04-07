use flux_attrs::*;

#[extern_spec]
#[refined_by(is_ok: bool)]
enum Result<T, E> {
    #[variant((T) -> Result<T, E>[true])]
    Ok(T),
    #[variant((E) -> Result<T, E>[false])]
    Err(E),
}

#[extern_spec]
impl<T, E> Result<T, E> {
    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/result.rs#L584
    #[no_panic]
    #[spec(fn(&Self[@b]) -> bool[b])]
    const fn is_ok(&self) -> bool;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/result.rs#L631
    #[no_panic]
    #[spec(fn(&Self[@b]) -> bool[!b])]
    const fn is_err(&self) -> bool;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/result.rs#L686
    #[no_panic]
    #[spec(fn(Result<T, E>[@b]) -> Option<T>[b])]
    fn ok(self) -> Option<T>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/result.rs#L709
    #[no_panic]
    #[spec(fn(Result<T, E>[@b]) -> Option<E>[!b])]
    fn err(self) -> Option<E>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/result.rs#L737
    #[no_panic]
    #[spec(fn(&Result<T, E>[@b]) -> Result<&T, &E>[b])]
    const fn as_ref(&self) -> Result<&T, &E>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/result.rs#L767
    #[no_panic]
    #[spec(fn(&mut Result<T, E>[@b]) -> Result<&mut T, &mut E>[b])]
    fn as_mut(&mut self) -> Result<&mut T, &mut E>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/result.rs#L799
    #[flux_rs::no_panic_if(F::no_panic())]
    #[spec(fn(Result<T, E>[@b], F) -> Result<U, E>[b] where F: FnOnce(T) -> U)]
    fn map<U, F: FnOnce(T) -> U>(self, op: F) -> Result<U, E>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/result.rs#L911
    #[flux_rs::no_panic_if(O::no_panic())]
    #[spec(fn(Result<T, E>[@b], O) -> Result<T, F>[b] where O: FnOnce(E) -> F)]
    fn map_err<F, O: FnOnce(E) -> F>(self, op: O) -> Result<T, F>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/result.rs#L1113
    #[spec(fn(Result<T, E>[true], &str) -> T)]
    fn expect(self, msg: &str) -> T
    where
        E: core::fmt::Debug;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/result.rs#L1161
    #[spec(fn(Result<T, E>[true]) -> T)]
    fn unwrap(self) -> T
    where
        E: core::fmt::Debug;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/result.rs#L1256
    #[spec(fn(Result<T, E>[false]) -> E)]
    fn unwrap_err(self) -> E
    where
        T: core::fmt::Debug;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/result.rs#L1225
    #[spec(fn(Result<T, E>[false], &str) -> E)]
    fn expect_err(self, msg: &str) -> E
    where
        T: core::fmt::Debug;
}
