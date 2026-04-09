#[flux::sig(fn(f: F) -> i32{v : v >= 1}
            where F: Fn(x: i32[@n]) -> i32[n + 1] requires n >= 0)]
fn test00<F>(_f: F) -> i32
where
    F: Fn(i32) -> i32,
{
    _f(0)
}

#[flux::sig(fn(f: F) -> i32[12]
    where F: Fn(x: &mut i32[@old]) ensures x : i32[old + 2]
)]
fn test01<F>(f: F) -> i32
where F : Fn(&mut i32) {
    let mut x = 0;
    f(&mut x);
    x + 10
}

#[flux_rs::spec(fn(y: &mut i32[@old]) ensures y: i32[(2 * (old + 1) - old)])]
fn inc2_mut(x: &mut i32) {
    *x += 2
}

#[flux_rs::spec(fn() -> i32[12])]
fn client01() -> i32 {
    test01(inc2_mut)
}

#[flux_rs::spec(fn(f: F) -> i32{ v: v >= 12}
    where F: Fn(old: i32) -> i32{v: v >= old + 2}
)]
fn test02<F>(f : F) -> i32
where F : Fn(i32) -> i32 {
    f(0) + 10
}


#[flux_rs::spec(fn(i32[@old]) -> i32[old + 2])]
fn inc2(x: i32) -> i32{
    x + 2
}

fn client02() -> i32 {
    test02(inc2)
}

#[flux_rs::spec(fn(f : F) -> i32[3]
    where F : Fn(i32[@old]) -> i32[old + 3]
)]
fn test03<F>(f: F) -> i32
where F : Fn(i32) -> i32 {
    f(0)
}