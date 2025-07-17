#![flux::specs {

   fn inc(n:i32) -> i32{v: n < v}

   fn id(n:i32) -> i32[n]

}]

pub fn inc(n: i32) -> i32 {
    n - 1 //~ ERROR refinement type
}

pub fn id(n: i32) -> i32 {
    n
}
