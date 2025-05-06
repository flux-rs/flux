#[flux::sig(fn (f: F) -> i32{v:10<=v}
            where F: FnOnce(i32{v:0 <= v}, i32{v:0<=v}) -> i32{v:0<=v}
        )]
pub fn test002_err<F>(f: F) -> i32
where
    F: FnOnce(i32, i32) -> i32,
{
    f(99, 100)
} //~ ERROR refinement type

#[flux::sig(fn (f: F) -> i32{v:0<=v}
            where F: FnOnce(i32{v:0 <= v}, i32{v:0<=v}) -> i32{v:10<=v}
        )]
pub fn test002<F>(f: F) -> i32
where
    F: FnOnce(i32, i32) -> i32,
{
    f(99, 100)
}

pub fn test002_client_err() {
    test002(|x, y| x + y); //~ ERROR refinement type
}
