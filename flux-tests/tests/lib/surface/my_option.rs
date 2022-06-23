#[flux::opaque]
#[flux::refined_by(b: bool)]
pub enum MyOption<T> {
    Some(T),
    None,
}

impl<T> MyOption<T> {
    #[flux::assume]
    #[flux::sig(fn(T) -> MyOption<T>[true])]
    pub fn some(val: T) -> MyOption<T> {
        MyOption::Some(val)
    }

    #[flux::assume]
    #[flux::sig(fn() -> MyOption<T>[false])]
    pub fn none() -> MyOption<T> {
        MyOption::None
    }

    #[flux::assume]
    #[flux::sig(fn(&MyOption<T>[@b]) -> bool[b])]
    pub fn is_some(&self) -> bool {
        matches!(self, MyOption::Some(_))
    }

    #[flux::assume]
    #[flux::sig(fn(MyOption<T>[true]) -> T)]
    pub fn unwrap(self) -> T {
        match self {
            MyOption::Some(v) => v,
            MyOption::None => panic!(),
        }
    }
}
