#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn (it: I) where I: Iterator<Item = i32[@n]>)] //~ ERROR illegal binder
pub fn foo<I>(_it: I)
where
    I: Iterator<Item = i32>,
{
}
