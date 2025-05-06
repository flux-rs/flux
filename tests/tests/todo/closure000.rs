#[flux::sig(fn (frog: F) -> i32{v:0<=v} where F: FnOnce(i32{v:0 <= v}) -> i32{v:0 <= v})]
fn test001<F>(frog: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    frog(99)
}

#[flux::sig(fn (frog: F) -> i32{v:0<=v} where F: FnOnce(i32{v:1000 <= v}) -> i32{v:0 <= v})]
fn test001_err<F>(frog: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    frog(99) //~ ERROR refinement type
}

fn test001_client() {
    test001(|x| x);
}

fn test001_client_err() {
    test001(|x| x - 1); //~ ERROR refinement type
}

// -------------------------------------------------------------------------
// #[flux::sig(fn (f: F) -> i32{v:0<=v}
//             where F: FnOnce(i32{v:0 <= v}) -> i32{v:0 <= v})]
// fn test0<F>(f: F) -> i32
// where
//     F: FnOnce(i32) -> i32,
// {
//     f(99)
// }

// #[flux::sig(fn (f: F) -> i32{v:0<=v}
//             where F: FnOnce(i32{v:0 <= v}, i32{v:0<=v})
//         )]
// fn test002<F>(f: F) -> i32
// where
//     F: FnOnce(i32, i32) -> i32,
// {
//     f(99, 100)
// }

// fn test002_client() {
//     test002(|x, y| x + y);
// }

// #[flux::sig(fn (f: F) -> i32[100]
//             where F: FnOnce(i32[@k]) -> i32[k+1])]
// fn test0<F>(f: F) -> i32
// where
//     F: FnOnce(i32) -> i32,
// {
//     f(99)
// }

// fn test0<F>(f: F) -> bool
// where
//     F: FnOnce(i32) -> bool,
// {
//     f(99)
// }

// fn client0_ok() -> bool {
//     test0(|k| k > 1)
// }

// fn test0<F>(f: F) -> i32
// where
//     F: for<'apple> FnOnce(&'apple i32) -> &'apple i32,
// {
//     let z = 99;
//     f(&z);
//     z
// }

// fn client0_ok() {
//     test0(|k| k);
// }
