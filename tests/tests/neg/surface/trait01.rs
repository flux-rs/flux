#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

pub fn foo<I>(it: I)
where
    I: Iterator<Item = i32>,
{
    for x in it {
        assert(0 <= x) //~ ERROR refinement type
    }
}
