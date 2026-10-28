pub struct A<T>(T);

// Returning a value that doesn't satisfy the revealed hidden type
#[flux::spec(fn() -> A<impl Iterator<Item = i32{v: v != 67}>>)]
pub fn test_return_impl_bad() -> A<impl Iterator<Item = i32>> {
    A(Some(67).into_iter()) //~ ERROR refinement type
}

pub struct B<T>(*mut T);

#[flux::spec(fn() -> B<impl Iterator<Item = i32{v: v < 5 || v > 50}>>)]
pub fn test_return_impl_ptr_bad() -> B<impl Iterator<Item = i32>> {
    B(Box::into_raw(Box::new(Some(23).into_iter()))) //~ ERROR refinement type
}

fn call_neg(t: (fn(i32),)) {
    (t.0)(-1)
}

#[flux::spec(fn(x: i32{x > 0}))]
fn pos_only(_x: i32) {}

pub fn test_reveal_fn_ptr(b: bool) -> impl Sized {
    if b {
        call_neg(test_reveal_fn_ptr(false));
    }
    (pos_only as fn(i32),) //~ ERROR refinement type
}

pub struct C<T>(fn(T));

pub trait TraitA {
    type Out;
    fn call(&self, x: Self::Out);
}

impl<T> TraitA for C<T> {
    type Out = T;
    fn call(&self, x: T) {
        (self.0)(x)
    }
}

#[flux::spec(fn() -> impl TraitA<Out = i32{v: v >= 0}>)]
pub fn test_reveal_contravariant() -> impl TraitA<Out = i32> {
    C(pos_only as fn(i32)) //~ ERROR refinement type
}

pub trait TraitB {
    type Out;
    fn get(self) -> Self::Out;
}

impl<T> TraitB for A<T> {
    type Out = T;
    fn get(self) -> T {
        self.0
    }
}

#[flux::spec(fn(A<i32{v: v > 0}>))]
fn requires_pos(_x: A<i32>) {}

// Using the result of a recursive call at the hidden type
pub fn test_rec(b: bool) -> impl TraitB {
    if b {
        requires_pos(test_rec(false)); //~ ERROR refinement type
    }
    A(-1)
}

#[flux::spec(fn(n: i32, x: A<i32{v: v >= n}>))]
fn takes_exact(_n: i32, _x: A<i32>) {}

#[flux::spec(fn(n: i32) -> impl TraitB<Out = i32{v: v >= n}>)]
pub fn test_rec_bound_bad(n: i32) -> impl TraitB<Out = i32> {
    if n > 0 {
        takes_exact(n, test_rec_bound_bad(n - 1)); //~ ERROR refinement type
    }
    A(n)
}

pub struct D<T, U>(T, U);

impl<T, U> TraitB for D<T, U> {
    type Out = T;
    fn get(self) -> T {
        self.0
    }
}

#[flux::spec(fn(D<i32, i32{v: v == 0}>))]
fn takes_tagged(_x: D<i32, i32>) {}

#[flux::spec(fn(n: i32) -> impl TraitB<Out = i32{v: v >= n}>)]
pub fn test_rec_tag_bad(n: i32) -> impl TraitB<Out = i32> {
    if n > 0 {
        takes_tagged(test_rec_tag_bad(n - 1)); //~ ERROR refinement type
    }
    D(n, 5)
}

pub struct E<T, U>(T, U);

pub trait TraitC {
    type A;
    type B;
    fn get_a(self) -> Self::A;
}

impl<T, U> TraitC for E<T, U> {
    type A = T;
    type B = U;
    fn get_a(self) -> T {
        self.0
    }
}

#[flux::spec(fn(E<i32, i32{v: v == 0}>))]
fn takes_p(_x: E<i32, i32>) {}

#[flux::spec(fn(n: i32) -> impl TraitC<A = i32{v: v >= n}>)]
pub fn test_rec_multi_bad(n: i32) -> impl TraitC<A = i32> {
    if n > 0 {
        takes_p(test_rec_multi_bad(n - 1)); //~ ERROR refinement type
    }
    E(n, 5)
}

#[flux::spec(fn(n: i32) -> impl TraitB<Out = i32{v: v >= n}>)]
pub fn test_rec_closure_bad(n: i32) -> impl TraitB<Out = i32> {
    let f = || takes_tagged(test_rec_closure_bad(n - 1)); //~ ERROR refinement type
    if n > 0 {
        f();
    }
    D(n, 5)
}

fn id<T>(x: T) -> T {
    x
}

// Returning the result of a recursive call
#[flux::spec(fn(n: i32) -> impl TraitB<Out = i32{v: v >= n}>)]
pub fn test_rec_id(n: i32) -> impl TraitB<Out = i32> {
    if n > 0 {
        return id::<A<i32>>(test_rec_id(n - 10));
    }
    A(n)
} //~ ERROR refinement type

#[flux::spec(fn(n: i32) -> impl TraitB<Out = i32{v: v >= n}>)]
pub fn test_rec_direct_bad(n: i32) -> impl TraitB<Out = i32> {
    if n > 0 {
        return test_rec_direct_bad(n - 10);
    }
    A(n)
} //~ ERROR refinement type

#[flux::spec(fn(n: i32) -> impl TraitB<Out = i32{v: v >= n}>)]
pub fn test_rec_inferred_bad(n: i32) -> impl TraitB<Out = i32> {
    if n > 0 {
        return id(test_rec_inferred_bad(n - 10));
    }
    A(n)
} //~ ERROR refinement type

#[flux::spec(fn(i32{v: v >= 5}))]
fn requires_ge5(_x: i32) {}

#[flux::spec(fn(i32{v: v < 5}))]
fn requires_lt5(_x: i32) {}

// Using the bounds outside the defining function
pub fn client() {
    requires_ge5(test_rec_id(5).get());
    requires_lt5(test_rec_id(5).get()); //~ ERROR refinement type
}

// Predicates around the opaque type are kept, both on a type and on a base generic argument
#[flux::spec(fn(n: i32) -> {impl Sized | n > 0})]
pub fn test_post_bad(n: i32) -> impl Sized {
    0 //~ ERROR refinement type
}

#[flux::spec(fn(n: i32) -> B<{impl Sized | n > 0}>)]
pub fn test_post_base_bad(n: i32) -> B<impl Sized> {
    B(std::ptr::null_mut::<i32>()) //~ ERROR refinement type
}

#[flux::spec(fn(i32{v: v > 5}) -> i32)]
fn gt5(x: i32) -> i32 {
    x
}

// `Fn` bounds are checked against the returned value
#[flux::spec(fn() -> impl Fn(i32{v: v > 0}) -> i32)]
pub fn test_fn_closure_bad() -> impl Fn(i32) -> i32 {
    |x| gt5(x) //~ ERROR refinement type
}

#[flux::spec(fn() -> impl Fn(i32{v: v > 0}) -> i32)]
pub fn test_fn_def_bad() -> impl Fn(i32) -> i32 {
    gt5 //~ ERROR refinement type
}

#[flux::spec(fn() -> impl Fn(i32) -> i32{v: v > 0})]
pub fn test_fn_output_bad() -> impl Fn(i32) -> i32 {
    |x| x //~ ERROR refinement type
}

// Coroutines are checked through their body
#[flux::spec(fn(b: bool) -> impl std::future::Future<Output = i32{v: v > 0}>)]
pub fn test_coroutine_bad(b: bool) -> impl std::future::Future<Output = i32> {
    if b {
        drop(test_coroutine_bad(false));
    }
    async { 0 } //~ ERROR refinement type
}
