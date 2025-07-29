#![allow(unused)]

#[flux::specs {

    impl Gromp for usize {  //~ ERROR unresolved trait implementation
      fn gromp() -> usize[0];
    }

}]
const _: () = ();
