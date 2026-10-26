pub struct Wrap<T>(T);
pub struct Token<T>(*mut T);
pub struct P<T, U>(T, U);

pub trait Tr {
    type Out;
    fn get(self) -> Self::Out;
}

impl<T> Tr for Wrap<T> {
    type Out = T;
    fn get(self) -> T {
        self.0
    }
}

pub trait Tr2 {
    type A;
    type B;
    fn get_a(self) -> Self::A;
}

impl<T, U> Tr2 for P<T, U> {
    type A = T;
    type B = U;
    fn get_a(self) -> T {
        self.0
    }
}

fn id<T>(x: T) -> T {
    x
}

#[flux::sig(fn(i32{v: v >= 5}))]
fn requires_ge5(_x: i32) {}

#[flux::sig(fn(Wrap<i32{v: v > 0}>))]
fn requires_pos(_x: Wrap<i32>) {}

#[flux::sig(fn(n: i32, x: Wrap<i32{v: v >= n}>))]
fn takes_exact(_n: i32, _x: Wrap<i32>) {}

#[flux::spec(fn(n: i32, x: Wrap<i32{v: v >= n - 20}>))]
fn wrap_bounded(_n: i32, _x: Wrap<i32>) {}

#[flux::sig(fn(P<i32, i32{v: v == 0}>))]
fn takes_both(_x: P<i32, i32>) {}

#[flux::sig(fn(i32{v: v > 0}) -> i32{v: v > 0})]
fn gt0(x: i32) -> i32 {
    x
}

// Returning a value that satisfies the bounds
#[flux::spec(fn() -> Wrap<impl Iterator<Item = i32[123]>>)]
pub fn test_return_impl() -> Wrap<impl Iterator<Item = i32>> {
    Wrap(Some(123).into_iter())
}

#[flux::spec(fn() -> Wrap<impl Iterator<Item = i32{v: v != 67}>>)]
pub fn test_return_impl_ok() -> Wrap<impl Iterator<Item = i32>> {
    Wrap(Some(68).into_iter())
}

#[flux::spec(fn() -> Wrap<impl Iterator<Item = i32{v: v < 5 || v > 50}>>)]
pub fn test_return_impl_disj() -> Wrap<impl Iterator<Item = i32>> {
    Wrap(Some(3).into_iter())
}

#[flux::spec(fn() -> Token<impl Iterator<Item = i32{v:1 <= v}>>)]
pub fn test_return_impl_ptr() -> Token<impl Iterator<Item = i32>> {
    Token(Box::into_raw(Box::new(Some(22).into_iter())))
}

pub fn spawn<F>(_future: impl FnOnce() -> F) -> Token<impl Sized> {
    Token(std::ptr::null_mut::<F>())
}

// Using the result of a recursive call at the hidden type
#[flux::spec(fn(b: bool) -> impl Tr<Out = i32{v: v > 0}>)]
pub fn test_rec_ok(b: bool) -> impl Tr<Out = i32> {
    if b {
        requires_pos(test_rec_ok(false));
    }
    Wrap(1)
}

#[flux::spec(fn(n: i32) -> impl Tr<Out = i32{v: v >= n}>)]
pub fn test_rec_bound(n: i32) -> impl Tr<Out = i32> {
    if n > 0 {
        wrap_bounded(n, test_rec_bound(n - 10));
    }
    Wrap(n)
}

#[flux::spec(fn(n: i32) -> impl Tr<Out = i32{v: v >= n}>)]
pub fn test_rec_bound_ok(n: i32) -> impl Tr<Out = i32> {
    if n > 0 {
        takes_exact(n - 1, test_rec_bound_ok(n - 1));
    }
    Wrap(n)
}

#[flux::spec(fn(n: i32) -> impl Tr2<A = i32{v: v >= n}, B = i32{v: v == 0}>)]
pub fn test_rec_multi_ok(n: i32) -> impl Tr2<A = i32> {
    if n > 0 {
        takes_both(test_rec_multi_ok(n - 1));
    }
    P(n, 0)
}

// Returning the result of a recursive call
#[flux::spec(fn(n: i32) -> impl Tr<Out = i32{v: v >= n}>)]
pub fn test_rec_direct_ok(n: i32) -> impl Tr<Out = i32> {
    if n > 0 {
        return test_rec_direct_ok(n);
    }
    Wrap(n)
}

#[flux::spec(fn(n: i32) -> impl Tr<Out = i32{v: v >= n}>)]
pub fn test_rec_inferred_ok(n: i32) -> impl Tr<Out = i32> {
    if n > 0 {
        return id(test_rec_inferred_ok(n));
    }
    Wrap(n)
}

// Using the bounds outside the defining function
pub fn test_client_ok() {
    requires_ge5(test_rec_direct_ok(5).get());
}

// Predicates around the opaque type are kept, both on a type and on a base generic argument
#[flux::spec(fn(n: i32{n > 0}) -> {impl Sized | n > 0})]
pub fn test_post_ok(n: i32) -> impl Sized {
    0
}

#[flux::spec(fn(n: i32{n > 0}) -> Token<{impl Sized | n > 0}>)]
pub fn test_post_base_ok(n: i32) -> Token<impl Sized> {
    Token(std::ptr::null_mut::<i32>())
}

// `Fn` bounds are checked against the returned value
#[flux::spec(fn() -> impl Fn(i32{v: v > 0}) -> i32{v: v > 0})]
pub fn test_fn_closure_ok() -> impl Fn(i32) -> i32 {
    |x| gt0(x)
}

#[flux::spec(fn() -> impl Fn(i32{v: v > 0}) -> i32{v: v > 0})]
pub fn test_fn_def_ok() -> impl Fn(i32) -> i32 {
    gt0
}

pub fn test_fn_client_ok() {
    test_fn_closure_ok()(1);
}

// Coroutines are checked through their body
#[flux::spec(fn(b: bool) -> impl std::future::Future<Output = i32{v: v > 0}>)]
pub fn test_coroutine_ok(b: bool) -> impl std::future::Future<Output = i32> {
    if b {
        drop(test_coroutine_ok(false));
    }
    async { 1 }
}
