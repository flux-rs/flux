use flux_attrs::*;

#[extern_spec]
#[refined_by(is_some: bool)]
enum Option<T> {
    #[variant(Option<T>[false])]
    None,
    #[variant((T) -> Option<T>[true])]
    Some(T),
}

#[extern_spec]
impl<T> Option<T> {
    #[sig(fn(&Self[@b]) -> bool[b])]
    const fn is_some(&self) -> bool;

    #[sig(fn(&Self[@b]) -> bool[!b])]
    const fn is_none(&self) -> bool;

    #[no_panic]
    #[sig(fn(Option<T>[true]) -> T)]
    const fn unwrap(self) -> T;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/option.rs#L957
    #[no_panic]
    #[spec(fn(Option<T>[true], &str) -> T)]
    const fn expect(self, msg: &str) -> T;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/option.rs#L1025
    #[no_panic]
    #[spec(fn(Option<T>[@b], T) -> T)]
    fn unwrap_or(self, default: T) -> T;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/option.rs#L1044
    #[flux_rs::no_panic_if(F::no_panic())]
    #[spec(fn(Option<T>[@b], F) -> T where F: FnOnce() -> T)]
    fn unwrap_or_else<F: FnOnce() -> T>(self, f: F) -> T;

    #[sig(fn(&Self[@b]) -> Option<&T>[b])]
    fn as_ref(&self) -> Option<&T>;

    #[sig(fn(&mut Self[@b]) -> Option<&mut T>[b])]
    fn as_mut(&mut self) -> Option<&mut T>;

    #[sig(fn(&Self[@b]) -> &[T][if b { 1 } else { 0 }])]
    fn as_slice(&self) -> &[T];

    #[sig(fn(&mut Self[@b]) -> &mut [T][if b { 1 } else { 0 }])]
    fn as_mut_slice(&mut self) -> &mut [T];

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/option.rs#L1465
    #[no_panic]
    #[spec(fn(Option<T>[@a], Option<U>[@b]) -> Option<U>[a && b])]
    fn and<U>(self, optb: Option<U>) -> Option<U>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/option.rs#L1581
    #[no_panic]
    #[spec(fn(Option<T>[@a], Option<T>[@b]) -> Option<T>[a || b])]
    fn or(self, optb: Option<T>) -> Option<T>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/option.rs#L1309
    #[no_panic]
    #[spec(fn(Option<T>[@b], E) -> Result<T, E>[b])]
    fn ok_or<E>(self, err: E) -> Result<T, E>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/option.rs#L1334
    #[flux_rs::no_panic_if(F::no_panic())]
    #[spec(fn(Option<T>[@b], F) -> Result<T, E>[b] where F: FnOnce() -> E)]
    fn ok_or_else<E, F: FnOnce() -> E>(self, err: F) -> Result<T, E>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/option.rs#L1504
    #[flux_rs::no_panic_if(F::no_panic())]
    #[spec(fn(Option<T>[@b], F) -> Option<U>{s: s => b} where F: FnOnce(T) -> Option<U>)]
    fn and_then<U, F: FnOnce(T) -> Option<U>>(self, f: F) -> Option<U>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/option.rs#L1783
    #[no_panic]
    #[spec(fn(self: &mut Option<T>[@b]) -> Option<T>[b]
           ensures self: Option<T>[false])]
    const fn take(&mut self) -> Option<T>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c6a955468b025dbe3d1de3e8f3e30496d1fb7f40/library/core/src/option.rs#L1841
    #[no_panic]
    #[spec(fn(self: &mut Option<T>[@b], T) -> Option<T>[b]
           ensures self: Option<T>[true])]
    const fn replace(&mut self, value: T) -> Option<T>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/option.rs#L1160
    #[flux_rs::no_panic_if(F::no_panic())]
    #[spec(fn(Option<T>[@b], F) -> Option<U>[b] where F: FnOnce(T) -> U)]
    fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Option<U>;

    /// Core impl: https://github.com/rust-lang/rust/blob/c871d09d1cc32a649f4c5177bb819646260ed120/library/core/src/option.rs#L1224
    #[flux_rs::no_panic_if(F::no_panic())]
    #[spec(fn(Option<T>[@b], U, F) -> U where F: FnOnce(T) -> U)]
    fn map_or<U, F: FnOnce(T) -> U>(self, default: U, f: F) -> U;
}
