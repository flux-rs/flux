#[flux_rs::refined_by(i: int)]
struct Wrapper {
    #[flux_rs::field(i32[i])]
    inner: i32,
}

impl Wrapper {
    #[flux_rs::spec(fn[hrn upd: (int, int) -> bool](s: &mut Self[@slf], f: F)
        ensures s : Self{v : upd(v, slf)}
        where F: Fn(x: &mut i32[@old]) ensures x : i32{v : upd(v, old)}
    )]
    fn with_mut<F>(&mut self, f: F)
    where
        F: Fn(&mut i32),
    {
        f(&mut self.inner);
    }
}

#[flux_rs::spec(fn(x: &mut i32[@old]) ensures x: i32[old + 1])]
fn inc(x: &mut i32) {
    *x += 1;
}

#[flux_rs::spec(fn() -> i32[100])]
fn test00() -> i32 {
    let mut w = Wrapper { inner: 99 };
    w.with_mut(inc);
    w.inner
}

#[flux_rs::spec(fn() -> i32[100])]
fn test01() -> i32 {
    let mut w = Wrapper { inner: 99 };
    w.with_mut(|x| *x += 1);
    w.inner
}

#[flux_rs::spec(fn() -> i32[100])]
fn test02() -> i32 {
    let mut w = Wrapper { inner: 99 };
    w.with_mut(|x| inc(x))
    w.inner
}
