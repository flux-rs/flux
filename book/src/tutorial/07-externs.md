# Extern Specifications

```rust, editable
#![feature(allocator_api)]
#![allow(unused)]
extern crate flux_rs;
use flux_rs::{attrs::*, extern_spec};
use std::alloc::{Allocator, Global};
use std::mem::swap;
```

```rust, editable, hidden
#[spec(fn (bool[true]))]
fn assert(b: bool) {
    if !b {
        panic!("assertion failed");
    }
}
```

No man is an island.

Every substantial Rust code base will make use
of *external crates*. To *check* properties of
such code bases, Flux requires some way to reason
about the uses of the external crate's APIs.

Let's look at how Flux lets you write
*assumptions*[^assumption] about the behavior of those
libraries via *extern specifications* (abbreviated to
*extern-specs*) which can then let us check facts about
the uses of the external crate's APIs.

To this end, flux lets you write extern-specs for

1. Functions,
2. Structs,
3. Enums,
4. Traits and their Impls.

In this chapter, we'll look at the first three,
and then we'll see how the idea [extends to traits
and their implementations](./08-traits.md).

## Extern Specs for Functions

As a first example, lets see how to write an extern spec for
the function `std::mem::swap`.

### Using Extern Functions

Lets write a little test that creates to references and swaps them

```rust,editable
pub fn test_swap() {
    let mut x = 5;
    let mut y = 10;
    std::mem::swap(&mut x, &mut y);
    assert(x == 10);
    assert(y == 5);
}
```

Now, if you push the **play button** you should see that Flux cannot prove
the two `assert`s. The little red squiggles indicate it does not know that
after the `swap` the values of `x` and `y` are swapped to `10` and `5`, as,
well, it has no idea about how `swap` behaves!

### Writing Extern Specs

We can fill this gap in flux's understanding by providing
an **extern-spec**  that gives flux a refined type
specification for `swap`

```rust,editable
#[extern_spec]
// UNCOMMENT THIS LINE to verify `test_swap`
// #[spec(fn(x: &mut T[@vx], y: &mut T[@vy]) ensures x: T[vy], y: T[vx])]
fn swap<T>(a: &mut T, b: &mut T);
```

**The refined specification** says that `swap` takes as input
two _mutable_ references `x` and `y` that refer to values of
type `T` with respective indices `vx` and `vy`. Upon finishing,
the types referred to by `x` and `y` are "swapped".

Now, if you uncomment and push play, flux will verify `test_swap` as
it knows that at the call-site, `vx` and `vy` are respectively `5` and `10`.

### Features of Extern Spec Functions

Note two things about the `extern_spec` specification.

1. First, up at the top, we had to import the `extern_spec` macro,
implemented in the `flux_rs` crate,
2. Second, importantly, we _do not write an implementation_ for the function,
as that is going to be taken from `std::mem`. Instead, we're just telling
flux to use the (uncommented) type specification when checking clients.


### Getting the Length of a Slice

Here is a function below that returns the `first` (well, `0`th)
element of a slice of `u32`s.

```rust,editable
fn first(slice: &[u32]) -> Option<u32> {
    let n = slice.len();
    if n > 0 {
        Some(slice[0])
    } else {
        None
    }
}
```

**EXERCISE** Unfortunately, flux does not know what `slice.len()` returns, and
so, cannot verify that the access `slice[0]` is safe! Can you help
it by *fixing* the `extern_spec` for the method shown below?
You might want to refresh your memory about the meaning of
`&[T][@n]` by quickly skimming the previous chapter on the [sizes of arrays
and slices](./06-consts.html#refined-compile-time-safety).

```rust, editable
#[extern_spec]
impl<T> [T] {
    #[spec(fn(&[T][@n]) -> usize)]
    fn len(v: &[T]) -> usize;
}
```

## Extern Specs for Enums: `Option`

In the [chapter on enums](./04-enums.html) we saw how you can
refine `enum` types with extra indices that track extra information
about the underlying value. For example, we saw how to implement
a [refined Option](./04-enums.html#a-refined-option) that is indexed
by a boolean that tracks whether the value is `Some` (and hence, safe
to `unwrap`)or `None`.

The `extern_spec` mechanism lets us do the same thing, but directly on
`std::option::Option`. To do so we need only

1. write extern-specs for the **enum definition** that add the indices
   and connect them to the variant constructors,
2. write extern-specs for the **method signatures** that let us use the
   indices to describe a refined API that is used to check client code.

### Extern Specs for the Type Definition

First, lets add the `bool` index to the `Option` type definition.

```rust,editable
#[extern_spec]
#[refined_by(valid: bool)]
enum Option<T> {
    #[variant(Option<T>[{valid: false}])]
    None,
    #[variant((T) -> Option<T>[{valid: true}])]
    Some(T),
}
```

As you might have noticed, this bit is *identical*
to the refined version of `Option` that we saw in
the [chapter on enums](./04-enums.html#a-refined-option),
except for the `#[extern_spec]` topping.

### Using the Type Definition

Adding the above "retrofits" the `bool` index directly
into the `std::option::Option` type. So, for example
we can write

```rust,editable
#[spec(fn () -> Option<i32>[{valid: true}])]
fn test_some() -> Option<i32> {
    Some(42)
}

#[spec(fn () -> Option<i32>[{valid: false}])]
fn test_none() -> Option<i32> {
    None
}
```

**TIP:** When there is a single field like `valid`
you can drop it, and just write `Option<i32>[true]`
or `Option<i32>[false]`.

### Extern Specs for Impl Methods

The extern specs become especially useful when we use them to refine
the methods that `impl`ement various key operations on `Option`s.

To do so, we can make an `extern_spec` `impl` for `Option`, much like
we did for slices, [back here](#getting-the-length-of-a-slice).

```rust,editable
#[extern_spec]
impl<T> Option<T> {
    #[sig(fn(&Option<T>[@b]) -> bool[b])]
    const fn is_some(&self) -> bool;

    #[sig(fn(&Option<T>[@b]) -> bool[!b])]
    const fn is_none(&self) -> bool;

    #[sig(fn(Option<T>[true]) -> T)]
    const fn unwrap(self) -> T;
}
```

The definition looks rather like the actual one,
except that it wears the `#[extern_spec]` attribute
on top, and the methods have no definitions, as we
want to use those from the extern crate, in this case,
the standard library.

Notice that the spec for

- `is_some` returns `true` if the input `Option` was indeed `valid`, i.e. was a `Some(..)`;
- `is_none` returns `true` if the input `Option` was *not* `valid`, i.e. was a `None`.

### Using Extern Method Specifications

We can test these new specifications out in our client code.

```rust,editable
fn test_opt_specs(){
    let a = Some(42);
    assert(a.is_some());
    let b: Option<i32> = None;
    assert(b.is_none());
}
```

### Safely Unwrapping

Of course, we all know that we _shouldn't_ directly use `unwrap`.
However, sometimes, its ok, if we somehow *know* that the value
is indeed a valid `Some(..)`. The refined type for `unwrap` keeps
us honest with a **precondition** that tells flux that it should
**only** be invoked when the underlying `Option` can be provably
`valid`.

```rust,editable
#[spec(fn (n:u32) -> Option<u8>)]
fn into_u8(n: u32) -> Option<u8> {
   if n <= 255 {
       Some(n as u8)
   } else {
       None
   }
}

fn test_unwrap() -> u8 {
    into_u8(42).unwrap()
}
```

**EXERCISE** The function `test_unwrap` above
merrily `unwrap`s the result of the call `into_u8`.
Flux is unhappy and flags an error even though surely
the call will not panic! The trouble is that the "default"
`spec` for `into_u8` -- the Rust type -- says it can
return *any* `Option<i32>`, including those that might
well blow up `unwrap`. Can you fix the `spec` for `into_u8`
so that flux verifies `test_unwrap`?

### A Safe Division Function

Lets write a safe-division function, that checks if the divisor
is non-zero before doing the division.

```rust,editable
#[spec(fn (num: u32, denom: u32) -> Option<u32[num / denom]>)]
pub fn safe_div(num: u32, denom: u32) -> Option<u32> {
    if denom == 0 {
        None
    } else {
        Some(num / denom)
    }
}
```

**EXERCISE** The client `test_safe_div` shown below is certainly it is safe to
divide by two! Alas, Flux thinks otherwise: it cannot determine that output of
`safe_div` may be safely `unwrap`ped. Can you figure out how to fix the specification
for `safe_div` so that the code below verifies?

```rust,editable
pub fn test_safe_div() {
    let res = safe_div(42, 2).unwrap();
    assert(res == 21);
}
```


## Extern Specs for Structs: `Vec`

Previously, we saw how to define a *new* type `RVec<T>`
for [refined vectors](./05-vectors.html) and to write
an API that let us track the vector's size, and hence
check the safety of vector accesses at compile time.
Next, lets see how we can use `extern_spec` to implement
(most of) the refined API directly on structs like
`std::vec::Vec` which are defined in external crates.

### Extern Specs for the Type Definition

As with `enum`s we start by sprinkling refinement
indices on the `struct` definition. Since we want
to track sizes, lets write

```rust,editable
#[extern_spec]
#[refined_by(len: int)]
#[invariant(0 <= len)]
struct Vec<T, A: Allocator = Global>;
```

### Extern Invariants

Note that we can additionally attach **invariants** to the `struct`
definition, which correspond to facts that are _always_ true about
the indices, for example, that the `len` of a `Vec` is always non-negative.

### Extern `struct`s are Opaque

Unlike with `enum`, the `extern_spec` is oblivious
to the _internals_ of the `struct`. That is flux
assumes that the fields are all "private", and so the
refinements must be tracked solely using the _methods_
used to construct and manipulate the `struct`.

The simplest of these is the one that births an *empty* `Vec`

```rust,editable
#[extern_spec]
impl<T> Vec<T> {
    #[spec(fn() -> Vec<T>[0])]
    fn new() -> Vec<T>;
}
```

We can test this out by creating an empty vector

```rust,editable
#[spec(fn () -> Vec<i32>[0])]
fn test_new() -> Vec<i32> {
    Vec::new()
}
```

### Extern Specs for Impl Methods

Lets beef up our refined `Vec` API with a few more methods
like `push`, `pop`, `len` and so on.

We might be tempted to just bundle them together with `new`
in the `impl` above, but it is important to Flux that the
the `extern_spec` implementations **mirror the original
implementations** so that Flux can accurately match (i.e. "resolve")
the `extern_spec` method with the original method, and thus,
attach the specification to uses of the original method.

As it happens, `push` and `pop` are defined in a *separate*
`impl` block, parameterized by a generic `A: Allocator`, so
our `extern_spec` mirrors this block:

```rust, editable
#[extern_spec]
impl<T, A: Allocator> Vec<T, A> {
    #[spec(fn(self: &mut Vec<T, A>[@n], T)
           ensures self: Vec<T, A>[n+1])]
    fn push(&mut self, value: T);

    #[spec(fn(self: &mut Vec<T, A>[@n]) -> Option<T>
           ensures self: Vec<T, A>[if n > 0 { n-1 } else { 0 }])]
    fn pop(&mut self) -> Option<T>;

    #[spec(fn(self: &Vec<T, A>[@n]) -> usize[n])]
    fn len(&self) -> usize;

    #[spec(fn(self: &Vec<T, A>) -> bool)]
    fn is_empty(&self) -> bool;
}
```

### Constructing Vectors

Lets take the refined `vec` API out for a spin.

```rust, editable
#[spec(fn() -> Vec<i32>[3])]
pub fn test_push() -> Vec<i32> {
    let mut res = Vec::new();   // res: Vec<i32>[0]
    res.push(10);               // res: Vec<i32>[1]
    res.push(20);               // res: Vec<i32>[2]
    res.push(30);               // res: Vec<i32>[3]
    assert(res.len() == 3);
    res
}
```

Flux uses the refinements to type `res` as a 0-sized `Vec<i32>[0]`.
Each subsequent `push` [updates the reference's type](./02-ownership.html#borrowing-updatable-references)
by increasing the size by one.
Finally, the `len` returns the size at that point, `3`, thereby
proving the assert.


### Testing Emptiness

**EXERCISE** Can you fix the spec for `is_empty` above so that the
two assertions below are verified?

```rust, editable
fn test_is_empty() {
   let v0 = test_new();
   assert(v0.is_empty());

   let v1 = test_push();
   assert(!v1.is_empty());
}
```

### The Refined `vec!` Macro

The ubiquitous `vec!` macro internally allocates a slice
and then calls `into_vec` to create a `Vec`.

```rust,editable
#[extern_spec]
impl<T> [T] {
    #[spec(fn(self: Box<[T], A>) -> Vec<T, A>)]
    fn into_vec<A>(self: Box<[T], A>) -> Vec<T, A>
    where
        A: Allocator;
}
```

**EXERCISE** Can you fix the `extern_spec` for `into_vec` so that
the code below verifies?

```rust, editable
#[spec(fn() -> Vec<i32>[3])]
pub fn test_push_macro() -> Vec<i32> {
    let res = vec![10, 20, 30];
    assert(res.len() == 3);
    res
}
```

### Pop-and-Unwrap

Suppose we wanted to write a function that popped the last element
of a non-empty vector.

```rust,editable
#[spec(fn (vec: &mut Vec<T>[@n]) -> T
       requires 0 < n
       ensures  vec: Vec<T>[n-1])]
fn pop_and_unwrap<T>(vec: &mut Vec<T>) -> T {
    vec.pop().unwrap()
}
```

**EXERCISE** Flux chafes because the spec for `pop` is too _weak_:
above does not tell us _when_ the returned value is safe to unwrap.
Can you go back and fix the spec for `fn pop` so that `pop_and_unwrap`
verifies?

### PopPop!

**EXERCISE** Finally, as a parting exercise, can you work out
why flux rejects the `pop2` function below, and modify the spec
so that it is accepted?

```rust,editable
#[spec(fn (vec: &mut Vec<T>[@n]) -> (T, T)
       ensures vec: Vec<T>[n-2] )]
fn pop2<T>(vec: &mut Vec<T>) -> (T, T)  {
    let v1 = pop_and_unwrap(vec);
    let v2 = pop_and_unwrap(vec);
    (v1, v2)
}
```

## Summary

Previously, we saw how to attach refined specifications for
[functions](./01-refinements.html), [structs](03-structs.html)
and [enums](04-enums.html).

In this chapter, we saw that you can use the `extern_spec`
mechanism to do the same things for objects defined elsewhere,
e.g. in external crates being used by your code.

Next, we'll learn how to use `extern_spec` to refine _traits_
(and their implementations), which is key to checking idiomatic
Rust code.


[^assumption]: We say *assumption* because we're presuming that
the actual code for the library is not available to verify; if
it was, you could of course actually *guarantee* that the library
correctly implements those specifications.
