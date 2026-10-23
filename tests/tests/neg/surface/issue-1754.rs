pub struct Wrap<T>(T);
pub struct Token<T>(*mut T);

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

#[flux::spec(fn() -> Wrap<impl Iterator<Item = i32{v: v != 67}>>)]
pub fn test_return_impl_bad() -> Wrap<impl Iterator<Item = i32>> {
    Wrap(Some(67).into_iter()) //~ ERROR refinement type
}

#[flux::spec(fn() -> Token<impl Iterator<Item = i32{v: v < 5 || v > 50}>>)]
pub fn test_return_impl_ptr_bad() -> Token<impl Iterator<Item = i32>> {
    Token(Box::into_raw(Box::new(Some(23).into_iter()))) //~ ERROR refinement type
}

#[flux::sig(fn(Wrap<i32{v: v > 0}>))]
fn requires_pos(_x: Wrap<i32>) {}

pub fn test_rec(b: bool) -> impl Tr {
    if b {
        requires_pos(test_rec(false)); //~ ERROR refinement type
    }
    Wrap(-1)
}

fn id<T>(x: T) -> T {
    x
}

#[flux::spec(fn(n: i32) -> impl Tr<Out = i32{v: v >= n}>)]
pub fn test_rec_id(n: i32) -> impl Tr<Out = i32> {
    if n > 0 { 
        return id::<Wrap<i32>>(test_rec_id(n - 10));
    }
    Wrap(n)
} //~ ERROR refinement type

#[flux::sig(fn(i32{v: v >= 5}))]
fn requires_ge5(_x: i32) {}

#[flux::sig(fn(i32{v: v < 5}))]
fn requires_lt5(_x: i32) {}

pub fn client() {
    requires_ge5(test_rec_id(5).get());
    requires_lt5(test_rec_id(5).get()); //~ ERROR refinement type
}

#[flux::sig(fn(n: i32, x: Wrap<i32{v: v >= n}>))]
fn takes_exact(_n: i32, _x: Wrap<i32>) {}

#[flux::spec(fn(n: i32) -> impl Tr<Out = i32{v: v >= n}>)]
pub fn test_rec_bound_bad(n: i32) -> impl Tr<Out = i32> {
    if n > 0 {
        takes_exact(n, test_rec_bound_bad(n - 1)); //~ ERROR refinement type
    }
    Wrap(n)
}

#[flux::spec(fn(n: i32) -> impl Tr<Out = i32{v: v >= n}>)]
pub fn test_rec_direct_bad(n: i32) -> impl Tr<Out = i32> {
    if n > 0 {
        return test_rec_direct_bad(n - 10);
    }
    Wrap(n)
} //~ ERROR refinement type

#[flux::spec(fn(n: i32) -> impl Tr<Out = i32{v: v >= n}>)]
pub fn test_rec_inferred_bad(n: i32) -> impl Tr<Out = i32> {
    if n > 0 {
        return id(test_rec_inferred_bad(n - 10));
    }
    Wrap(n)
} //~ ERROR refinement type

pub struct W2<T, U>(T, U);

impl<T, U> Tr for W2<T, U> {
    type Out = T;
    fn get(self) -> T {
        self.0
    }
}

#[flux::sig(fn(W2<i32, i32{v: v == 0}>))]
fn takes_tagged(_x: W2<i32, i32>) {}

#[flux::spec(fn(n: i32) -> impl Tr<Out = i32{v: v >= n}>)]
pub fn test_rec_tag_bad(n: i32) -> impl Tr<Out = i32> {
    if n > 0 {
        takes_tagged(test_rec_tag_bad(n - 1)); //~ ERROR refinement type
    }
    W2(n, 5)
}

#[flux::spec(fn(n: i32) -> impl Tr<Out = i32{v: v >= n}>)]
pub fn test_rec_closure_bad(n: i32) -> impl Tr<Out = i32> {
    let f = || takes_tagged(test_rec_closure_bad(n - 1)); //~ ERROR refinement type
    if n > 0 {
        f();
    }
    W2(n, 5)
}

pub struct P<T, U>(T, U);

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

#[flux::sig(fn(P<i32, i32{v: v == 0}>))]
fn takes_p(_x: P<i32, i32>) {}

#[flux::spec(fn(n: i32) -> impl Tr2<A = i32{v: v >= n}>)]
pub fn test_rec_multi_bad(n: i32) -> impl Tr2<A = i32> {
    if n > 0 {
        takes_p(test_rec_multi_bad(n - 1)); //~ ERROR refinement type
    }
    P(n, 5)
}

// Unpinned refinements in the hidden type are revealed as `true`, so the returned value must be
// checked against that, e.g., here callers could otherwise call `pos_only` with any `i32`.
#[flux::sig(fn(x: i32{x > 0}))]
fn pos_only(_x: i32) {}

fn call_neg(t: (fn(i32),)) {
    (t.0)(-1)
}

pub fn test_reveal_fn_ptr(b: bool) -> impl Sized {
    if b {
        call_neg(test_reveal_fn_ptr(false));
    }
    (pos_only as fn(i32),) //~ ERROR refinement type
}

// The associated type sits in a contravariant position of the hidden type, so it's not enough to
// check that the returned value's `Out` is a subtype of the bound.
pub struct FnArg<T>(fn(T));

pub trait Call {
    type Out;
    fn call(&self, x: Self::Out);
}

impl<T> Call for FnArg<T> {
    type Out = T;
    fn call(&self, x: T) {
        (self.0)(x)
    }
}

#[flux::spec(fn() -> impl Call<Out = i32{v: v >= 0}>)]
pub fn test_reveal_contravariant() -> impl Call<Out = i32> {
    FnArg(pos_only as fn(i32)) //~ ERROR refinement type
}

pub fn test_reveal_contravariant_client() {
    test_reveal_contravariant().call(0);
}
