#![allow(unused)]

#[flux::specs {

    impl From<u32> for busize { //~ ERROR unresolved item
      fn gromp() -> usize[0];
    }
}]
const _: () = ();
