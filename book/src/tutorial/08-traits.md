# Traits and Associated Refinements

```rust, editable
#![allow(unused)]
extern crate flux_rs;
use flux_rs::{attrs::*, extern_spec};
use std::ops::Range;
```

```rust, editable, hidden
#[spec(fn (bool[true]))]
fn assert(b: bool) {
    if !b {
        panic!("assertion failed");
    }
}
```

One of Rust's most appealing features is its **trait** system which lets us decouple
**descriptions** of particular operations that a type should support, from their actual
*implementations*. This mechanism lets us to write *generic* code that works for all
the particular implementations of the trait interface.

Traits are ubiquitous in Rust code. For example,

- an addition `x + y` is internally represented as `x.add(y)`
  where `x` and `y` can be values that implement the `Add` trait,
  allowing for a uniform way to write `+` that is just works across
  all compatible types;

- an indexing operation `x[i]` is internally represented as `x.index(i)`
  where `x` can be any value that implements the `Index` trait, and `i`
  a compatible "key", which allows for a standard way to lookup
  containers at a particular value;

- a loop `for x in e { ... }` becomes `while let Some(x) = e.next() { ... }`,
  where the `e` can be any value that implements the `Iterator` trait,
  allowing for an elegant and uniform way to iterate over different kinds
  of ranges and collections.

In this chapter, lets learn how traits pose some interesting challenges
for formal verification, and how Flux solves these challenges using
a technique called **associated refinements**.

## A Trait to `Index` Values

To get to the essence of the challenge that traits pose for formal verification,
lets write our own little `Index` trait. (The real ones in the standard library
have a few more moving parts that unnecessarily complicate the exposition.)

```rust, editable
pub trait Index<Idx> {
    type Output:?Sized;

    fn index(&self, index: Idx) -> &Self::Output;
}
```

The above snippet defines a `trait` called `Index` that is parameterized by `Idx`: the
type used as the actual index. To *implement* the trait, we must specify

1. The `Self` type for the container itself (e.g. a slice, a vector, hash-map, a string, *etc.*),
2. The `Idx` type used as the index (e.g. a `usize` or `String` key, or `Range<usize`, *etc*), and
3. The `Output`: an *associated type* that describes what the `index` method returns, and finally,
4. The `index` method itself, which takes a reference to `self` and an `index` of type `Idx`, and returns a reference to the `Output`.

We can now write functions that work over *any* type that implements `Index`.
For instance, the `get_first` method will let use borrow the first (i.e. `0`th)
element of any `container` that implements `Index<usize>`. (Lets ignore the
`#[trusted]` for now, it just tells flux to quietly accept this code without
protest.)


```rust, editable
#[trusted]
fn get_first<A, T: Index<usize, Output = A>>(container: &T) -> &A {
    container.index(0)
}
```

## Indexing Slices with `usize`

To *use* the `trait`, we must actually *implement* it for some particular type.
For example, lets write an implementation to `index` a slice by a `usize` value:

```rust, editable
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
```

The above code describes an implementation where the

- `Self` type of the *container* is a slice `[A]`;
- `Idx` type of the *index* is `usize`;
- `Output` returned by `index()` is a (reference to) `A`; and
- `index()` is just a wrapper around the standard library's implementation.

## Problem: Yikes `index` is unsafe!

Oh dear, the "indirection" through `index` has introduced a problem!

<!-- ```rust, editable
fn test_slice() {
    let empty_slice: &[i32] = &[];
    let x0 = empty_slice[0];       // rejected by flux
    let x0 = empty_slice.index(0); // accepted by flux!

    // let nonempty_slice: &[i32] = &[1, 2, 3];
    // let x = s.index(1);
    // assert_eq!(*x, 2);
}
```
 -->

```rust, editable
fn canary() {
    assert(10 > 20);
}
```



```rust, editable
#[flux::specs {
  trait Index<Idx> {
    #[reft]
    fn valid(me: Self, index: Idx) -> bool { true };

    fn index(&Self[@me], index:Idx{<Self as Index<Idx>>::valid(me, index)}) -> &Self::Output;
  }}]
const _: () = ();
```

```
## Challenge: How to Specify _Safe_ Indexing

### `trait` is too *high*
### `impl` is too *low*

## Solution: Associated Refinements

### TRAIT

### IMPL

## Examples


// `Vec` with `usize` -------------------------------------------------------------------------

#[assoc(fn valid(me: Vec, index: int) -> bool { index < me.len })]
impl <A:Copy> Index<usize> for Vec<A> {
    type Output = A;

    #[spec(fn(&Self[@me], index:usize{<Vec<A> as Index<usize>>::valid(me, index)}) -> &Self::Output)]
    fn index(&self, index: usize) -> &Self::Output {
        &self[index]
    }
}

#[spec(fn (xs: &Vec<f64>[@n], ys: &Vec<f64>[n]) -> f64)]
fn dot_vec(xs: &Vec<f64>, ys: &Vec<f64>) -> f64 {
    let mut res = 0.0;
    for i in 0..xs.len() {
        res += xs.index(i) * ys.index(i);
    }
    res
}


// Slice with usize ----------------------------------------------------------------------------

#[assoc(fn valid(n: int, index: int) -> bool { index < n })]
impl <A:Copy> Index<usize> for [A] {
    type Output = A;

    #[spec(fn(&Self[@n], index:usize{<[A] as Index<usize>>::valid(n, index)}) -> &Self::Output)]
    fn index(&self, index: usize) -> &Self::Output {
        &self[index]
    }
}

#[spec(fn (xs: &[f64][@n], ys: &[f64][n]) -> f64)]
fn dot_slice(xs: &[f64], ys: &[f64]) -> f64 {
    let mut res = 0.0;
    for i in 0..xs.len() {
        res += xs.index(i) * ys.index(i);
    }
    res
}

// `Vec` with `Range` ----------------------------------------------------------------------------

#[assoc(fn valid(me: Vec, index: Range<int>) -> bool {
    index.start <= index.end && index.end <= me.len
})]
impl <A> Index<Range<usize>> for Vec<A> {

    type Output = [A];

    #[spec(fn(&Self[@me], index:Range<usize>{<Vec<A> as Index<Range<usize>>>::valid(me, index)}) -> &Self::Output)]
    fn index(&self, index: Range<usize>) -> &Self::Output {
        &self[index.start..index.end]
    }
}

// `str` with `Range` ----------------------------------------------------------------------------
#[assoc(fn valid(me: str, index: Range<int>) -> bool {
    index.start <= index.end && index.end <= str_len(me)
})]
impl Index<Range<usize>> for str  {

    type Output = str;

    #[spec(fn(&Self[@me], index:Range<usize>{<str as Index<Range<usize>>>::valid(me, index)}) -> &Self::Output)]
    fn index(&self, index: Range<usize>) -> &Self::Output {
        &self[index.start..index.end]
    }
}

fn test_str() {
    let cat = "caterpillar";
    let sub = cat.index(0..6); // OK
    let sub = cat.index(0..19); // Error
}
```