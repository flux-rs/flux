#![allow(unused)]

#[flux::specs {

    impl Gromp for usize {  //~ ERROR unresolved
      fn gromp() -> usize[0];
    }

}]
const _: () = ();
