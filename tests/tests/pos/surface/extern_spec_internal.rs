#[flux::extern_spec]
#[flux::sig(fn(&T) -> &[T][1])]
fn from_ref<T>(s: &T) -> &[T] {
    std::slice::from_ref::<T>(s)
}

#[flux::sig(fn(&i32) -> &[i32]{n: n > 0})]
pub fn test(x: &i32) -> &[i32] {
    from_ref(x)
}
