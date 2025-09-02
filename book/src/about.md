#![allow(unused)]
extern crate flux_rs;
use flux_rs::{attrs::*, extern_spec};
use std::ops::Range;
#[spec(fn (bool[true]))]
fn assert(b: bool) {
    if !b {
        panic!("assertion failed");
    }
}
pub trait Index<Idx> {
    type Output:?Sized;

    fn index(&self, index: Idx) -> &Self::Output;
}
#[trusted]
fn get_first<A, T: Index<usize, Output = A>>(container: &T) -> &A {
    container.index(0)
}
// #[assoc(fn valid(me: Vec, index: int) -> bool { index < me.len })]
impl <A> Index<usize> for [A] {

    type Output = A;

    // #[spec(fn(&Self[@me], index:usize{<Vec<A> as Index<usize>>::valid(me, index)}) -> &Self::Output)]
    // fn index(&self, index: usize) -> &Self::Output {
    //     &self[index]
    // }

    // #[spec(fn(&Self[@n], index:usize{<[A] as Index<usize>>::valid(n, index)}) -> &Self::Output)]
    fn index(&self, index: usize) -> &Self::Output {
        &self[index]
    }
}
fn canary() {
    assert(10 > 20);
}
#[flux::specs {
  trait Index<Idx> {
    #[reft]
    fn valid(me: Self, index: Idx) -> bool { true };

    fn index(&Self[@me], index:Idx{<Self as Index<Idx>>::valid(me, index)}) -> &Self::Output;
  }}]
const _: () = ();

# About Flux

<img src="img/logo-wide.svg" class="flux-logo" alt="Flux Logo">

## Team

Flux is being developed by

* [Nico Lehmann](https://github.com/nilehmann),
* [Adam Geller](https://www.cs.ubc.ca/~atgeller/)
* [Cole Kurashige](https://www.cole-k.com/)
* [Gilles Barthe](https://gbarthe.github.io/)
* [Niki Vazou](https://nikivazou.github.io/)
* [Ranjit Jhala](https://cseweb.ucsd.edu/~rjhala)

## Code

Flux is open-source and available [here](http://github.com/liquid-rust/flux)

## Publications

* [Lehmann, Nico, Adam T. Geller, Niki Vazou, and Ranjit Jhala. "Flux: Liquid types for rust."  PLDI (2023)](https://dl.acm.org/doi/pdf/10.1145/3591283)
* [Lehmann, Nico, Cole Kurashige, Nikhil Akiti, Niroop Krishnakumar, and Ranjit Jhala. "Generic Refinement Types." POPL (2025)](https://dl.acm.org/doi/pdf/10.1145/3704885)

## Talks

* [PLDI'23](https://www.youtube.com/watch?v=3iYt2JTXCwM)
* [SOAP'23](https://www.youtube.com/watch?v=NIJtZ0yUDX0)

## Thanks

This work was supported by the National Science Foundation, European Research Council,
and by generous gifts from Microsoft Research.

[pldi23-paper]: https://ranjitjhala.github.io/static/flux-pldi23.pdf
[popl25-paper]: https://ranjitjhala.github.io/static/flux-popl25.pdf
[pldi23-talk]: https://www.youtube.com/watch?v=3iYt2JTXCwM

## Limitations

This is a prototype! Use at your own risk. Everything could break and it will break.
