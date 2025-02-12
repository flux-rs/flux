mod iter;

use flux_attrs::*;

#[extern_spec(core::slice)]
impl<T> [T] {
    #[sig(fn(&Self[@n]) -> usize[n])]
    fn len(&self) -> usize;

    #[sig(fn(&Self[@n]) -> bool[n == 0])]
    fn is_empty(&self) -> bool;

    #[sig(fn(&Self[@n]) -> Option<&T>[n != 0])]
    fn first(&self) -> Option<&T>;

    #[sig(fn(&Self[@n]) -> Iter<T>[0, n])]
    fn iter(&self) -> Iter<'_, T>;
}

#[cfg(flux_sysroot_test)]
mod tests {
    #![allow(dead_code)]

    use flux_attrs::*;

    #[sig(fn(bool[true]))]
    fn assert(_: bool) {}

    #[should_fail]
    fn test01(xs: &[i32]) {
        let _x = xs[0];
    }

    fn test_len(xs: &[i32]) {
        if xs.len() > 0 {
            let _x = xs[0];
        }
    }

    fn test_is_empty(xs: &[i32]) {
        if !xs.is_empty() {
            let _x = xs[0];
        }
    }

    fn test_first00(xs: &[i32]) {
        if xs.len() > 0 {
            assert(xs.first().is_some());
        }
        if xs.is_empty() {
            assert(xs.first().is_none());
        }
    }

    #[should_fail]
    fn test_first01(xs: &[i32]) {
        assert(xs.first().is_some());
    }

    fn test_iter00(xs: &[i32]) {
        let it = xs.iter();
        let ys = it.as_slice();
        assert(xs.len() == ys.len());
    }
}
