#[flux::trusted]
fn map<T, R, F>(bloop: &Option<T>, closure: F) -> Option<R>
where
    F: FnOnce(&mut T) -> R,
{
    todo!()
}

pub fn test2(c: Option<&mut [i32]>) {
    map(&c, |arr| stuff(arr));
    map(&c, |arr| for v in arr.iter_mut() {});
}

#[flux::trusted]
pub fn stuff(arr: &mut [i32]) {}
