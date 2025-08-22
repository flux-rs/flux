#![allow(unused)]

#[flux::specs {

    impl Gromp for usize {  //~ ERROR unresolved item
      fn gromp() -> usize[0];
    }

}]
const _: () = ();
