# Traits and Associated Refinements

```rust, editable
#![allow(unused)]
extern crate flux_rs;
extern crate flux_core;
extern crate flux_alloc;
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
**implementations**, to enable *generic* code that works across all implementations of
an interface.

Traits are ubiquitous in Rust code. For example,

- an _addition_ `x + y` is internally represented as `x.add(y)`
  where `x` and `y` can be values that implement the `Add` trait,
  allowing for a uniform way to write `+` that works across
  all compatible types;

- an _indexing_ operation `x[i]` is internally represented as `x.index(i)`
  where `x` can be any value that implements the `Index` trait, and `i`
  a compatible "key", which allows for a standard way to lookup
  containers at a particular value;

- an _iteration_ `for x in e { ... }` becomes `while let Some(x) = e.next() { ... }`,
  where the `e` can be any value that implements the `Iterator` trait,
  allowing for an elegant and uniform way to iterate over different kinds
  of ranges and collections.

In this chapter, lets learn how traits pose some interesting
puzzles for formal verification, and how Flux resolves these
challenges with **associated refinements**.

## First things First

To limber up before we get to traits, lets
write a function to return (a reference to)
the first element of a slice.

```rust, editable
fn get_first_slice<A>(container: &[A]) -> &A
{
    &container[0]
}
```

The method `get_first_slice` works just
fine if you call it on _non-empty_ slices,
but will panic at run-time if you try it on
an empty one

```rust, editable
fn test_first_slice() {
    let s0: &[i32] = &[10, 20, 30];
    let v0 = get_first_slice(s0);
    println!("get_first_slice {s0:?} ==> {v0}");

    let s1: &[char] = &['a', 'b', 'c'];
    let v1 = get_first_slice(s1);
    println!("get_first_slice {s1:?} ==> {v1}");

    let s2: &[bool] = &[];
    let v2 = get_first_slice(s2);
    println!("get_first_slice {s2:?} ==> {v2}");
}
```

### Catching Panics at Compile Time

You might recall from [this previous chapter](06-consts.html#refined-compile-time-safety)
that Flux tracks the sizes of arrays and slices.

If you click the check button, you will see that flux
disapproves of `get_first_slice`

```
error[E0999]: assertion might fail: possible out of bounds access

   |
13 |    &container[0];
   |    ^^^^^^^^^^^^
```

### Specifying Non-Empty Slices

**EXERCISE** Can you go back and add a flux `spec` for `get_first_slice` that says that the function
should  _only_ be called with _non-empty_ slices? The spec should look something like the below, except
the `...` should be a constraint over `size`.

```
#[spec(fn (container: &[A]{size: ...}) -> &A)]
```

When you are done, you should see no warnings in `get_first_slice` but you will get an error in
`test_first_slice`, precisely at the location where we call it with an empty slice, which you
can fix by commenting out or removing the last call...

## A Trait to `Index` Values

Next, lets write our own little trait to index different kinds of containers [^1].



```rust, editable
pub trait IndexV1<Idx> {
    type Output:?Sized;

    fn index(&self, index: Idx) -> &Self::Output;
}
```

The above snippet defines a `trait` called `IndexV1` that is parameterized by `Idx`: the
type used as the actual index. To *implement* the trait, we must specify

1. The `Self` type for the container itself (e.g. a slice, a vector, hash-map, a string, *etc.*),
2. The `Idx` type used as the index (e.g. a `usize` or `String` key, or `Range<usize>`, *etc*), and
3. The `Output`: an *associated type* that describes what the `index` method returns, and finally,
4. The `index` method itself, which takes a reference to `self` and an `index` of type `Idx`, and returns a reference to the `Output`.

### A Generic, Reusable `get_firstV1`

We can now write functions that work over *any* type that implements the `Index` trait.
For instance, we can generalize the `get_first_slice` method, which only worked on slices,
to the `get_firstV1` method will let use borrow the `0`th element of _any_ `container` that
implements `Index<usize>`.

```rust, editable
fn get_firstV1<A, T>(container: &T) -> &A
  where
    T: ?Sized + IndexV1<usize, Output = A>
{
    container.index(0)
}
```

### Indexing Slices with `usize`

To use the `trait`, we must actually *implement* it for particular types of interest.

Lets implement a method to `index` a slice by a `usize` value:


```rust, editable
#[trusted]
impl <A> IndexV1<usize> for [A] {

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

Lets ignore the `#[trusted]` for now: it just tells flux to accept this code
without protesting about `self[index]` triggering an out-of-bounds error.

### Testing `get_firstV1`

Sweet! Now that we have a concrete implementation for `Index`
we should be able to _test_ it

```rust, editable
fn test_firstV1() {
    let s0: &[i32] = &[10, 20, 30];
    let v0 = get_firstV1(s0);
    println!("get_firstV1 {s0:?} ==> {v0}");

    let s1: &[char] = &['a', 'b', 'c'];
    let v1 = get_firstV1(s1);
    println!("get_firstV1 {s1:?} ==> {v1}");

    let s2: &[bool] = &[];
    let v2 = get_firstV1(s2);
    println!("get_firstV1 {s2:?} ==> {v2}");
}
```

Click the run button. Huh?! No warnings??

Of course, the last one _will_ panic.

But why didn't flux _warn_ us about it, like it did with `test_first_slice`.

### Yikes `get_firstV1` is unsafe!

When we *directly* access a slice as in `get_first_slice`,
or `test_first_slice`, flux complains about the potential,
in this case, _certain_, out of bounds access.

But the *indirection* through `get_firstV1` (and `index`) has
has laundered the out of bounds access, tricking
flux into unsoundly missing the run-time error!

We're in a bit of a pickle.

The `Index` trait _giveth_ the ability to write *generic*
code like `get_firstV1`, but apparently _taketh away_ the
ability to *catch panics* at compile-time.

Surely, there is a way to use traits without giving up
on compile-time verification...

### The Challenge: How to Specify _Safe_ Indexing, Generically

Clearly we _should not_ call `get_firstV1` with empty slices.

The method `get_firstV1` wants to access the `0`-th element
of the container, and will crash at run-time if the `0`th element
does not exist, as is the case with an empty slice.

But the puzzle is this: how do we specify
**"the `0`-th element exists"** for _any_
generic `container` that implements `Index`?

## Associated Refinements

Flux's solution to this puzzle is to borrow a page from Rust's own playbook.

Lets revisit the definition of the `Index` trait:

```
pub trait IndexV1<Idx> {
    type Output:?Sized;
    fn index(&self, index: Idx) -> &Self::Output;
}
```

In the above, `Output` is an **associated type** for the `Index` trait that
specifies what the `index` method returns. For instance, in our implementation
of `Index<usize>` for slices `[A]`, the `Output` is `A`.
Inspired this idea, Flux extends traits with the ability to specify
**associated refinements** that can _describe_ the values accepted
and returned by the trait's methods.

### Valid Indexes

Thus, we can extend the trait with an associated refinement
that specifies when an index is `valid` for a container.
Lets do so by defining the `Index` trait as:

```rust, editable
#[reft(fn valid(me: Self, index: Idx) -> bool)]
pub trait Index<Idx:?Sized> {
    type Output:?Sized;

    #[spec(fn(&Self[@me], idx:Idx{<Self as Index<Idx>>::valid(me, idx)}) -> &Self::Output)]
    fn index(&self, idx: Idx) -> &Self::Output;
}
```

There are _two_ new things in our new version of `Index`.

**1. Declaration**
First, the `reft` attribute declares[^2] the _associated refinement_:
a refinement level function named `valid`, that

- _takes_ as inputs, the `Self` type of the container and the `Idx` type of the index, and
- _returns_ a `bool` which indicates if the `index` is valid for the container.


**2. Use**
Next, the `spec` attribute refines the `index` method to say that it should only be
passed an `idx` that is *valid* for the `me` container, where `valid` is the associated
refinement declared above. The notation `<Self as Index<Idx>>::valid(me, idx)` is a
(sadly, verbose!) way to refer to the `valid` function associated with the particular
implementation of the `Index` trait for the `Self` type.


### A Safe (and Generic, Reusable) `get_first`

We can now write functions that work over *any* type that implements the `Index` trait,
but where flux will guarantee that `index` is safe to call. For example, lets revisit
the `get_first` method that returns the 0th element of a container.

```rust, editable
// #[spec(fn (&T{container:<T as Index<usize>>::valid(container, 0)}) -> &A)]
fn get_first<A, T>(container: &T) -> &A
  where T: ?Sized + Index<usize, Output = A>
{
    container.index(0)
}
```

Aha, now flux complains that the above is _unsafe_ because we don't know that `container`
is _actually_ `valid` for the index `0`. To make it safe, we must add (uncomment!) the
flux specification in the line above. This spec says that `get_first` can only be called
with a `container` that is `valid` for the index `0`.

### Indexing Slices with `usize`

Lets now revisit that implementation of for slices using `usize` indexes.

```rust, editable
#[assoc(fn valid(size: int, index: int) -> bool { index < size })]
impl <A> Index<usize> for [A] {

    type Output = A;

    #[spec(fn(&Self[@me], idx:usize{<[A] as Index<usize>>::valid(me, idx)}) -> &Self::Output)]
    fn index(&self, index: usize) -> &Self::Output {
        &self[index]
    }
}
```

As with the trait definition, there are two new things in our implementation of `Index` for slices.

**1. Implementation**
First, we provide a concrete implementation of the _associated refinement_ `valid`.
Recall that in flux, slices `[A]` are [represented by their size](./06-consts.html#refined-compile-time-safety) at the refinement level.
Hence, the implementation of `valid` takes as parameters the `size`
of the slice and the `index`, and returns `true` exactly if
the `index` is less than the `size`.

**2. Use**
As with the trait method, the actual implementation of the `index`
method has been refined to say that it should only be passed an
`idx` that is *valid* for `me` at the specified `idx`.[^3]

### Testing `get_first`

Now, lets revisit our clients for `get_first` using the new `Index` trait.

```rust, editable
fn test_first() {
    let s0: &[i32] = &[10, 20, 30];
    let v0 = get_first(s0);
    println!("get_first {s0:?} ==> {v0}");

    let s1: &[char] = &['a', 'b', 'c'];
    let v1 = get_first(s1);
    println!("get_first {s1:?} ==> {v1}");

    let s2: &[bool] = &[];
    let v2 = get_first(s2);
    println!("get_first {s2:?} ==> {v2}");
}
```

_Hooray!_ Now, when you click the check button, flux will complain about the
last call to `get_first` because the slice `s2` is _not_ `valid` for the index `0`!
To do so, flux _specialized_ the specification of `get_first` (which required
`container` to be `valid` for `0`) with the actual _definition_ of `valid` for
slices (which requires that `0 < size`) and the actual `size` for `s2` (which is `0`).
As `0 < 0` is false, flux rejects the code at compile time.


## Indexing Strings with Ranges

The whole point of the `Index` trait is be able to `index` _different kinds_ of
containers. Lets see how to implement `Index` for `str` using `Range<usize>` indexes,
which return sub-slices of the string.

```rust, editable
#[assoc(fn valid(me: str, index: Range) -> bool {
    index.start <= index.end && index.end <= str_len(me)
})]
impl Index<Range<usize>> for str  {

    type Output = str;

    #[spec(fn(&Self[@me], idx:Range<usize>{<str as Index<Range<usize>>>::valid(me, idx)}) -> &Self::Output)]
    fn index(&self, idx: Range<usize>) -> &Self::Output {
        &self[idx.start..idx.end]
    }
}
```

The implementation above, implements `Index<Range<usize>>` for `str` by

1. **Defining** the associated refinement `valid` to say that a `Range` is valid for a string
   if the `start` of the range is less than or equal to the `end`, and the `end` is
   less than or equal to the length of the string (which we get using the built-in
   `str_len` function);

2. **Refining** the specification of the `index` method to say that it should only be
   passed an `index` that is valid for the string `me`; and the given `idx`.

Now when we run flux on clients of this implementation,
we can see that the first call is a valid sub-slice, but the
second is _not_ and hence, is rejected by flux.

```rust, editable
fn test_str() {
    let cat = "caterpillar";
    let sub = cat.index(0..6); // OK
    let sub = cat.index(0..19); // Error
}
```

Flux produces the error pinpointing the problem:

```
error[E0999]: refinement type error
   |
89 |     let sub = cat.index(0..19); // Error
   |               ^^^^^^^^^^^^^^^^ a precondition cannot be proved
   |
note: this is the condition that cannot be proved
   |
74 |     index.start <= index.end && index.end <= str_len(me)
   |                                 ^^^^^^^^^^^^^^^^^^^^^^^^
```

**EXERCISE** Can you modify the code above so that the second call to `index`
is accepted by flux?

## Indexing Vectors with `usize`

**EXERCISE** Let's implement the `Index` trait for `Vec` using `usize` indexes.
The definition of `valid` is too permissive, can you modify it so that flux accepts
the below `impl`?


```rust, editable
#[assoc(fn valid(me: Vec, index: int) -> bool { true })]
impl <A:Copy> Index<usize> for Vec<A> {
    type Output = A;

    #[spec(fn(&Self[@me], index:usize{<Vec<A> as Index<usize>>::valid(me, index)}) -> &Self::Output)]
    fn index(&self, index: usize) -> &Self::Output {
        &self[index]
    }
}
```

**EXERCISE** Let's write a client that uses the `index` on `Vec`
to compute a dot-product for two `Vec<f64>`. Can you fix the `spec`
for `dot_vec` so flux accepts it?

```rust, editable
#[spec(fn (xs: &Vec<f64>, ys: &Vec<f64>) -> f64)]
fn dot_vec(xs: &Vec<f64>, ys: &Vec<f64>) -> f64 {
    let mut res = 0.0;
    for i in 0..xs.len() {
        res += xs.index(i) * ys.index(i);
    }
    res
}
```

## Indexing Vectors with Ranges

**EXERCISE** Finally, lets extract _sub-slices_ from vectors using `Range<usize>` indexes.
Why does flux reject the below `impl`? Can you edit the code so flux accepts it?

```rust, editable
#[assoc(fn valid(me: Vec, idx: Range<int>) -> bool {
    true
  })]
impl <A> Index<Range<usize>> for Vec<A> {

    type Output = [A];

    #[spec(fn(&Self[@me], idx:Range<usize>{<Vec<A> as Index<Range<usize>>>::valid(me, idx)}) -> &Self::Output)]
    fn index(&self, idx: Range<usize>) -> &Self::Output {
        &self[idx.start..idx.end]
    }
}
```

## Conclusion

In this chapter, we saw how traits can be extended with **associated refinements**
which let us _declare_ refinements on the inputs and outputs of trait methods
(e.g. `valid` indexes) that are then _implemented_  by each implementation of
the trait (e.g. the index is less than the slice size).

Associated refinements turn out to be an extremely useful mechanism, for example,
they let us specify properties of commonly used operations like
[indexing](spec-index) and [iteration](spec-iterator), and more
advanced properties like the semantics of sql queries [^4] and
the behavior of memory allocators [^5].


[^1]: The "real" ones in the standard library have a few more moving parts that would needlessly complicate our explanation of the interaction between traits and formal verification.

[^2]: `valid` function is just a declaration: we do not specify an actual _body_
as those will be filled in by the implementors of the trait. We could specify a
_default_ body for `valid` e.g. which always returns `true`, which can be
_over-ridden_ i.e. redefined by implementations, but we must be careful
about what we choose as the default.

[^3]: By the way, it seems a little silly to _repeat_ the spec for `index` doesn't it?
To be sound, Flux checks that the implementation needs to be a [subtype of the trait method](https://en.wikipedia.org/wiki/Covariance_and_contravariance_(computer_science)).
We could for example, accept _more_ inputs and produce _fewer_ outputs.
But in this case, it is simply a version of the trait specification, specialized
to the particular `Self` and `Idx` types of the implementation.

[spec-index]: https://github.com/flux-rs/flux/blob/main/lib/flux-core/src/slice/index.rs#L20

[spec-iterator]: https://github.com/flux-rs/flux/blob/main/lib/flux-core/src/iter/traits/iterator.rs#L10-L16

[^4]: See section 6.2 of this [POPL 2025 paper](https://ranjitjhala.github.io/static/popl25-generic-refinements.pdf) for more details.

[^5]: See this [SOSP 2025 paper](https://ranjitjhala.github.io/static/sosp25-ticktock.pdf) for more details.
