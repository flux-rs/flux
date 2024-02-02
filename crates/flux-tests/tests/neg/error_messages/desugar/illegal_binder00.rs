#[flux::sig(fn(&[i32[@n]]))] //~ ERROR illegal binder
fn hipa(x: &[i32]) {}

#[flux::sig(fn(Option<i32[@n]>))] //~ ERROR illegal binder
fn ira(x: Option<i32>) {}

#[flux::sig(fn(i32) -> i32[@n])] //~ ERROR illegal binder
pub fn myint2(x: i32) -> i32 {
    x
}

#[flux::sig(fn(i32[#x]))] //~ ERROR illegal binder
fn test01(x: i32) {}

#[flux::sig(fn (it: I) where I: Iterator<Item = i32[@n]>)] //~ ERROR illegal binder
pub fn foo<I>(_it: I)
where
    I: Iterator<Item = i32>,
{
}

#[flux::refined_by(b: int)]
pub enum E2 {
    #[flux::variant((i32[@n]) -> E2[@n])] //~ ERROR illegal binder
    A(i32),
}
