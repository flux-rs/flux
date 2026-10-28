pub struct A<T>(T);

// The returned value satisfies the bounds
#[flux::spec(fn() -> A<impl Iterator<Item = i32[123]>>)]
pub fn test_return_impl() -> A<impl Iterator<Item = i32>> {
    A(Some(123).into_iter())
}

#[flux::spec(fn() -> A<impl Iterator<Item = i32{v: v != 67}>>)]
pub fn test_return_impl_neq() -> A<impl Iterator<Item = i32>> {
    A(Some(68).into_iter())
}

#[flux::spec(fn() -> A<impl Iterator<Item = i32{v: v < 5 || v > 50}>>)]
pub fn test_return_impl_disj() -> A<impl Iterator<Item = i32>> {
    A(Some(3).into_iter())
}

pub struct B<T>(*mut T);

#[flux::spec(fn() -> B<impl Iterator<Item = i32{v:1 <= v}>>)]
pub fn test_return_impl_ptr() -> B<impl Iterator<Item = i32>> {
    B(Box::into_raw(Box::new(Some(22).into_iter())))
}

// The hidden type can mention type parameters
pub fn spawn<F>(_future: impl FnOnce() -> F) -> B<impl Sized> {
    B(std::ptr::null_mut::<F>())
}

pub trait TraitA {
    type Out;
    fn get(self) -> Self::Out;
}

impl<T> TraitA for A<T> {
    type Out = T;
    fn get(self) -> T {
        self.0
    }
}

#[flux::spec(fn(A<i32{v: v > 0}>))]
fn requires_pos(_x: A<i32>) {}

// Inside the defining function, a recursive call can be used at the hidden type
#[flux::spec(fn(b: bool) -> impl TraitA<Out = i32{v: v > 0}>)]
pub fn test_rec(b: bool) -> impl TraitA<Out = i32> {
    if b {
        requires_pos(test_rec(false));
    }
    A(1)
}

#[flux::spec(fn(n: i32, x: A<i32{v: v >= n - 20}>))]
fn wrap_bounded(_n: i32, _x: A<i32>) {}

#[flux::spec(fn(n: i32) -> impl TraitA<Out = i32{v: v >= n}>)]
pub fn test_rec_bound(n: i32) -> impl TraitA<Out = i32> {
    if n > 0 {
        wrap_bounded(n, test_rec_bound(n - 10));
    }
    A(n)
}

#[flux::spec(fn(n: i32, x: A<i32{v: v >= n}>))]
fn takes_exact(_n: i32, _x: A<i32>) {}

#[flux::spec(fn(n: i32) -> impl TraitA<Out = i32{v: v >= n}>)]
pub fn test_rec_bound_exact(n: i32) -> impl TraitA<Out = i32> {
    if n > 0 {
        takes_exact(n - 1, test_rec_bound_exact(n - 1));
    }
    A(n)
}

pub struct C<T, U>(T, U);

pub trait TraitB {
    type A;
    type B;
    fn get_a(self) -> Self::A;
}

impl<T, U> TraitB for C<T, U> {
    type A = T;
    type B = U;
    fn get_a(self) -> T {
        self.0
    }
}

#[flux::spec(fn(C<i32, i32{v: v == 0}>))]
fn takes_both(_x: C<i32, i32>) {}

#[flux::spec(fn(n: i32) -> impl TraitB<A = i32{v: v >= n}, B = i32{v: v == 0}>)]
pub fn test_rec_multi(n: i32) -> impl TraitB<A = i32> {
    if n > 0 {
        takes_both(test_rec_multi(n - 1));
    }
    C(n, 0)
}

// Returning a recursive call, directly or through a generic function
#[flux::spec(fn(n: i32) -> impl TraitA<Out = i32{v: v >= n}>)]
pub fn test_rec_direct(n: i32) -> impl TraitA<Out = i32> {
    if n > 0 {
        return test_rec_direct(n);
    }
    A(n)
}

fn id<T>(x: T) -> T {
    x
}

#[flux::spec(fn(n: i32) -> impl TraitA<Out = i32{v: v >= n}>)]
pub fn test_rec_inferred(n: i32) -> impl TraitA<Out = i32> {
    if n > 0 {
        return id(test_rec_inferred(n));
    }
    A(n)
}

#[flux::spec(fn(i32{v: v >= 5}))]
fn requires_ge5(_x: i32) {}

// Outside the defining function, the bounds are known
pub fn test_client() {
    requires_ge5(test_rec_direct(5).get());
}

// Predicates on the opaque type are kept, on a type and on a generic argument
#[flux::spec(fn(n: i32{n > 0}) -> {impl Sized | n > 0})]
pub fn test_post(n: i32) -> impl Sized {
    0
}

#[flux::spec(fn(n: i32{n > 0}) -> B<{impl Sized | n > 0}>)]
pub fn test_post_base(n: i32) -> B<impl Sized> {
    B(std::ptr::null_mut::<i32>())
}

#[flux::spec(fn(i32{v: v > 0}) -> i32{v: v > 0})]
fn gt0(x: i32) -> i32 {
    x
}

// `Fn` bounds hold for the returned value
#[flux::spec(fn() -> impl Fn(i32{v: v > 0}) -> i32{v: v > 0})]
pub fn test_fn_closure() -> impl Fn(i32) -> i32 {
    |x| gt0(x)
}

#[flux::spec(fn() -> impl Fn(i32{v: v > 0}) -> i32{v: v > 0})]
pub fn test_fn_def() -> impl Fn(i32) -> i32 {
    gt0
}

pub fn test_fn_client() {
    test_fn_closure()(1);
}
