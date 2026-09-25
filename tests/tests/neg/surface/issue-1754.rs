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
        return id::<Wrap<i32>>(test_rec_id(n - 10)); //~ ERROR refinement type
    }
    Wrap(n)
}

#[flux::sig(fn(i32{v: v >= 5}))]
fn requires_ge5(_x: i32) {}

pub fn client() {
    requires_ge5(test_rec_id(5).get()); //~ ERROR refinement type
}

#[flux::spec(fn(n: i32) -> impl Tr<Out = i32{v: v >= n}>)]
pub fn test_rec_closure(n: i32) -> impl Tr<Out = i32> {
    let clo = |nn: i32| {
        test_rec_closure(0)
    };
    if n > 0 {
        return clo(n + 1); //~ ERROR refinement type
    }
    Wrap(n)
}
