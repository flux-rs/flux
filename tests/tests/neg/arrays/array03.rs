struct S {
    #[flux::field(i32{v: v > 0})]
    f: i32,
}

#[flux::sig(fn([S; 1]) -> i32{v: v > 1})]
fn test01(arr: [S; 1]) -> i32 {
    let a = &arr[0];
    a.f //~ ERROR refinement type error
}

#[flux::sig(fn([S; 1]) -> i32{v: v > 0})]
fn test02(mut arr: [S; 1]) -> i32 {
    let a = &mut arr[0];
    a.f = 0; //~ ERROR assignment might be unsafe
    a.f
}
