# Extern Specifications

```rust, editable
#![allow(unused)]
extern crate flux_rs;
use flux_rs::{assert, attrs::*, extern_spec};
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

1. Standalone functions,
2. Structs,
3. Enums,
4. Traits and their Impls.

In this chapter, we'll look at the first three,
and then we'll see how the idea [extends to traits
and their implementations](./08-traits.md).

## Extern Specs for Functions

As a first example, lets see how to write an extern spec for
the function `std::mem::swap`.

```rust,editable
use std::mem::swap;
```

### Using Extern Functions

Lets write a little test that creates to references and swaps them

```rust,editable
pub fn test_swap() {
    let mut x = 5;
    let mut y = 10;
    swap(&mut x, &mut y);
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
type `T` with respective indices `vx` and `vy`, and upon finishing,
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

```rust, editable
#[extern_spec]
impl<T> [T] {
    #[spec(fn(&[T][@n]) -> usize)]
    fn len(v: &[T]) -> usize;
}
```

**HINT:** You might want to refresh your memory about the meaning of
`&[T][@n]` by quickly skimming the previous [chapter on the sizes of arrays
and slices](./06-consts.html#refined-compile-time-safety).
http://localhost:3001/tutorial/06-consts.html#refined-compile-time-safety

## Extern Specs for Enums: `Option`

In the [chapter on enums](./04-enums.html) we saw how you can
refine `enum` types with extra indices that track extra information
about the underlying value. For example, we saw how to implement
a [refined Option](./04-enums.html#a-refined-option) that is indexed
by a boolean that tracks whether the value is `Some` (and hence, safe
to `unwrap`)or `None`.

The `extern_spec` mechanism lets us do the same thing, but directly on
`std::option::Option`. To do so we need only

1. write extern-specs for the *enum definition* that add the indices
   and connect them to the variant constructors,
2. write extern-specs for the *method signatures* that let us use the
   indices to describe a refined API that is used to check client code.

### Extern Specs for the Type Definition

First, lets add the `bool` index to the `Option` type definition.

```rust,editable
#[extern_spec]
#[refined_by(valid: bool)]
enum Option<T> {
    #[variant((T) -> Option<T>[{valid: true}])]
    Some(T),
    #[variant(Option<T>[{valid: false}])]
    None,
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
the methods that `impl` the various key operations on `Option`s.

To do so, we can make an `extern impl` for `Option` (much like
we did for slices, [back here](#getting-the-length-of-a-slice)

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

The definition mirrors the actual one, except that it
wears the `#[extern_spec]` attribute on top, and the
methods have no definitions (as we want to use those
from the extern crate, i.e. the standard library.

### Using Extern Method Specifications

We can test these new specifications out in our client code.

```rust,editable
fn test_opt_specs(){
    let a = Some(42);
    assert(a.is_some());
    let b: Option<i32> = None;
    assert(b.is_none());
    let c = a.unwrap();
    assert(c == 42);
}
```

### A Safe Indexing Function

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

**EXERCISE** Look at this client that uses `safe_div` --- surely it is safe to
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

- struct : tests/neg/extern_specs/extern_spec_impl.rs
- both : vec00.rs



[^assumption]: We say *assumption* because we're presuming that
the actual code for the library is not available to verify; if
it was, you could of course actually *guarantee* that the library
correctly implements those specifications.
