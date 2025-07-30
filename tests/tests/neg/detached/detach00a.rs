pub fn inc(n: i32) -> i32 {
    n - 1 //~ ERROR refinement type
}

pub fn id(n: i32) -> i32 {
    n
}

pub fn blah(b: bool) -> i32 {
    if b { inc(1) } else { id(1) }
}

#[flux::specs {

   fn inc(n:i32) -> i32{v: n < v};
   fn id(n:i32) -> i32[n];

}]
const _: () = ();
