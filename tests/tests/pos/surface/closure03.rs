#[flux::trusted]
fn map<T, R, F>(_bloop: &Option<T>, _closure: F) -> Option<R>
where
    F: FnOnce(&mut T) -> R,
{
    todo!()
}

pub fn test2(c: Option<&mut [i32]>) {
    map(&c, |arr| stuff(arr));
    // map(&c, |arr| for v in arr.iter_mut() {});
}

#[flux::trusted]
pub fn stuff(_arr: &mut [i32]) {}
