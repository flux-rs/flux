#[flux::sig(fn (f: F) -> i32{v:0<=v}
            where F: FnOnce(i32{v:0 <= v}) -> i32{v:0 <= v})]
fn test0<F>(f: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(99)
}

#[flux::sig(fn () -> i32{v:0<=v})]
fn client0_ok() -> i32 {
    test0(|k| k + 1)
}

fn client00_err() -> i32 {
    test0(|k| k - 1)
}

// ----------------------------------------------------------------------

#[flux::sig(fn (f: F) -> i32[100]
            where F: FnOnce(i32[@k]) -> i32[k+1])]
fn test1<F>(f: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(99)
}

#[flux::sig(fn () -> i32[100])]
fn client1_ok() -> i32 {
    test1(|k| k + 1)
}

#[flux::sig(fn () -> i32[100])]
fn client0_err() -> i32 {
    test1(|k| k - 1)
}

// ----------------------------------------------------------------------

#[flux::sig(fn (n: i32, f: F) -> i32{v: n <= v}
            where F: FnOnce(i32{v:n <= v}) -> i32{v:n <= v})]
fn test2<F>(n: i32, f: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(n)
}

#[flux::sig(fn () -> i32{v:1000 <= v})]
fn client2_ok() -> i32 {
    test2(1000, |k| k + 1)
}

#[flux::sig(fn () -> i32{v:1000 <= v})]
fn client2_err_a() -> i32 {
    test2(1000, |k| k - 1)
}

#[flux::sig(fn () -> i32{v:1000 <= v})]
fn client2_err_b() -> i32 {
    test2(10, |k| k - 1)
}

// ----------------------------------------------------------------------

#[flux::sig(fn (n: i32, f: F) -> i32{v: v <= n}
            where F: FnOnce({i32[@k] | k < n}) -> i32[k+1])]
fn test3<F>(n: i32, f: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(n)
}

#[flux::sig(fn () -> i32{v:v <= 1000})]
fn client3_ok() -> i32 {
    test3(1000, |k| k + 1)
}

#[flux::sig(fn () -> i32{v:v <= 1000})]
fn client3_err_a() -> i32 {
    test3(1000, |k| k - 1)
}

#[flux::sig(fn () -> i32{v:v <= 10})]
fn client3_err_b() -> i32 {
    test3(1000, |k| k - 1)
}
