#[flux::sig(fn () -> impl Iterator<Item = i32{v:100<=v}>)]
pub fn test_fail() -> impl Iterator<Item = i32> {
    Some(10).into_iter() //~ ERROR refinement type
}

#[flux::sig(fn () -> impl Iterator<Item = i32{v:1<=v}>)]
pub fn test_pass() -> impl Iterator<Item = i32> {
    Some(10).into_iter()
}

#[flux::sig(fn () -> Option<i32{v:10<=v}>)]
pub fn test_client() -> Option<i32> {
    let mut it = test_pass();
    it.next()
} //~ ERROR refinement type
