#![flux::specs {

   fn inc(n:i32) -> i32{v: n < v};
   fn id(n:i32) -> i32[n]; //~ ERROR unresolved name `id`

}]

pub fn inc(n: i32) -> i32 {
    n + 1
}
