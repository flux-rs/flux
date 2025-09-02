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
*descriptions* of particular operations that a type should support, from their actual
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

## First things First

To limber up before we get to traits, lets
write a function to return (a reference to)
the first element of a slice.

```rust, editable
fn get_first_slice(container: &[A]) -> &A
{
    container[0]
}
```

The method `get_first_slice` works just
fine if you call it on _non-empty_ slices,
but will panic at run-time if you try it on
an empty one

```rust
fn test_first_slice() {
    let s0: &[i32] = &[10, 20, 30];
    let v0 = get_first_slice(s0);
    println!("get_first {s0} ==> {v0}");

    let s1: &[char] = &['a', 'b', 'c'];
    let v1 = get_first_slice(s1);
    println!("get_first {s1} ==> {v1}");

    let s2: &[bool] = &[];
    let v2 = get_first_slice(s2);
    println!("get_first {s2} ==> {v2}");
}
```

### Catching Panics at Compile Time

You might recall from this [previous chapter](06-consts.html#refined-compile-time-safety)
that Flux tracks the sizes of arrays and slices.

If you click the check button, you will see that flux
disapproves of `get_first_slice`, intoning

```
error[E0999]: assertion might fail: possible out of bounds access

   |
14 |    container[0];
   |    ^^^^^^^^^^^^
```

### Specifying Non-Empty Slices

**EXERCISE** Can you write a flux `spec` for
`get_first_slice` that says that the function
should  _only_ be called with _non-empty_ slices?
The spec should look something like the below,
except the `...` should be a constraint over `len`.

```
#[spec(fn (container: &[A]{len: ...}) -> &A)]
```

When you are done, you should see no warnings in
`get_first_slice` but you will get an error in
`test_first_slice`, precisely at the location
where we call it with an empty slice.

## A Trait to `Index` Values

Next, lets write our own little trait to `Index`
different kinds of containers [^1].


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

### A Generic, Reusable `get_first`

We can now write functions that work over *any* type that implements the `Index` trait.
For instance, we can generalize the `get_first_slice` method --- which only
worked on slices --- to the `get_first` method will let use borrow the first
(i.e. `0`th, sigh) element of any `container` that implements `Index<usize>`.

```rust, editable
fn get_first<A, T>(container: &T) -> &A
  where T: ?Sized + Index<usize, Output = A>
{
    container.index(0)
}
```

### Indexing Slices with `usize`

To use the `trait`, we must actually *implement* it
for particular types of interest. Lets implement a
method to `index` a slice by a `usize` value:

```rust, editable
#[trusted]
impl <A> Index<usize> for [A] {

    type Output = A;

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

(Lets ignore the `#[trusted]` for now: it just tells flux to accept this code
without protesting about `self[index]` triggering an out-of-bounds error.)

### Running `get_first`

Sweet! Now that we have a concrete implementation for `Index`
we should be able to _test_ it

```rust
fn test_first() {
    let s0: &[i32] = &[10, 20, 30];
    let v0 = get_first(s0);
    println!("get_first {s0} ==> {v0}");

    let s1: &[char] = &['a', 'b', 'c'];
    let v1 = get_first(s1);
    println!("get_first {s1} ==> {v1}");

    let s2: &[bool] = &[];
    let v2 = get_first(s2);
    println!("get_first {s2} ==> {v2}");
}
```

Huh?!

Of course, the last one will panic.

But why didn't flux _warn_ us about it, like it did with `test_first_slice`.

### Yikes `get_first` is unsafe!

When we *directly* access a slice as in `get_first_slice`,
(or, if you did the exercise, `test_first_slice`) flux complains
about the potential (in this case, certain!) out of bounds access.

But the *indirection* through `get_first` (and `index`) has
has laundered the out of bounds access, tricking
flux into unsoundly missing the run-time error!

We're in a bit of a pickle.

The `Index` trait _giveth_ the ability to write *generic*
code like `get_first`, but apparently _taketh away_ the
ability to *catch panics* at compile-time.

Surely, there is a way to use traits without giving up
on compile-time verification...

### The Challenge: How to Specify _Safe_ Indexing, Generically

Clearly we _should not_ call `get_first` with empty slices.

The method `get_first` wants to access the `0`-th element
of the container, and will crash at run-time if the `0`th element
does not exist, as is the case with an empty slice.

But the puzzle is this: how do we specify
**"the `0`-th element exists"** for any
generic `container` that implements `Index`?

## Associated Refinements

- valid
- trait
- get_first
- impl

## Other Clients

- Vec/usize [ EX ]

- Str/Range

- Vec/Range [ EX ]


```rust, editable
fn canary() {
    assert(10 > 20);
}
```
<!--

PLDI 2023
https://dl.acm.org/doi/pdf/10.1145/3591283

ICFP 2023
https://dl.acm.org/doi/pdf/10.1145/3607845

POPL 2024
https://dl.acm.org/doi/pdf/10.1145/3632912

SOSP 2024
https://ranjitjhala.github.io/static/icarus-sosp24.pdf

ICSE 2025
https://ranjitjhala.github.io/static/icse25-neurosymbolic-refinement-inference.pdf

SOSP 2025
https://ranjitjhala.github.io/static/sosp25-ticktock.pdf


```rust, editable
// #[flux::specs {
//   trait Index<Idx> {
//     #[reft]
//     fn valid(me: Self, index: Idx) -> bool { true }

//     fn index(&Self[@me], index:Idx{<Self as Index<Idx>>::valid(me, index)}) -> &Self::Output;
//   }}]
// const _: () = ();
```

## Solution: Associated Refinements

### TRAIT

### IMPL

## Examples


Perhaps we shouldn't have been so *trusting* of the `index`
implementation above. Indeed, go ahead and _remove_ the line
`#[trusted]` attribute and hit the check button. When you
do so, flux will immediately wag its finger

```
error[E0999]: assertion might fail: possible out of bounds access

   |
25 |        &self[index]
   |         ^^^^^^^^^^^
```

Indeed, flux finds that implementation of `.index()` rather sketchy
because it cannot prove that `index` is within the bounds of `self`.

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
``` -->

[^1]: The "real" ones in the standard library have a few more moving parts that would needlessly complicate our explanation of the interaction between traits and formal verification.
