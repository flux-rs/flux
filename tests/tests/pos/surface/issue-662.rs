pub fn baz(v: &mut Vec<i32>) {
    v.iter_mut().for_each(|x| *x *= 2);
}
