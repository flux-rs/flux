# Ownership in Flux

```rust, editable, hidden
#![allow(unused)]
extern crate flux_rs;
use flux_rs::attrs::*;
```

[Online demo](https://flux.goto.ucsd.edu/?example=ownership.rs)

[Previously](./01-introducing-flux.md) we saw how to refine basic Rust
types like `i32` and `bool` with _indices_ and _constraints_ to
constrain the set of values described by those types. For instance, we
wrote the function `assert` function which can _only_ be called with `true`

```rust,editable
#[flux_rs::spec(fn (bool[true]))]
fn assert(b: bool) {
    if !b {
        panic!("assertion failed");
    }
}

fn test_assert() {
    assert(2 + 2 == 4);
    assert(2 + 2 == 5); // fails to type check
}
```

The whole point of Rust, of course, is to allow for efficient
imperative _sharing_ and _updates_, via the clever type system
that keeps an eye on the _ownership_ of resources to make sure
that aliasing and mutation cannot happen at the same time.

Next, lets see how Flux melds refinements and Rust's ownership
mechanisms to make refinements pleasant in the imperative setting.

<!-- SLIDE -->

## Exclusive Ownership

Rust's most basic form of sharing is _exclusive_ ownership,
in which exactly one variable in a function has the right to
mutate a memory location. When a location is exclusively
owned, we can be sure that there are _no other references_
to it. Consequently, `flux` can _update_ the type to precisely
track the value whenever the location is changed.

For example, consider the program

```rust, editable
#[flux_rs::spec(fn () -> i32[3])]
pub fn mk_three() -> i32 {
  let mut r = 0;  // r: i32[0]
  r += 1;
  assert(r == 1); // r: i32[1]
  r += 1;
  assert(r == 2); // r: i32[2]
  r += 1;
  assert(r == 3); // r: i32[3]
  r
}
```

The variable `r` has _different types_ at each point inside `mk_three`.
It starts off as `i32[0]`. The first increment changes it to `i32[1]`,
then `i32[2]` and finally, the returned type `i32[3]`.

<!-- SLIDE -->

## Exclusive Ownership and Loops

This exclusive ownership mechanism is at work in the `factorial` example
we signed off with [previously](./01-introducing-flux.md)

```rust, editable
#[flux_rs::spec(fn (n:i32{0 <= n}) -> i32{v:n <= v})]
pub fn factorial(n: i32) -> i32 {
    let mut i = 0;  // i: i32[0]
    let mut r = 1;  // r: i32[1]
    while i < n {
                    // i: i32{v:0 <= v <= n}
                    // r: i32{v:1 <= v && i <= v}
        i += 1;
        r = r * i;
    }
    r
}
```

In the above code, `i` and `r` start off at `0` and `1` but then
flux _infers_ (a story for another day) that inside the `while`-loop[^1]

- `i` has type `i32{v:0<=v && v < n}`
- `r` has type `i32{v:1<=v && i <= v}`

and hence, upon exit since `i == n` we get that the result is at least `n`.

<!-- SLIDE -->

## Borrowing: Shared References

Exclusive ownership suffices for simple local updates
like in `factorial`. However, for more complex data,
functions must temporarily relinquish ownership to
allow _other_ functions to mutate the data.

Rust cleverly allows this via the notion of
_borrowing_ using two kinds of references
that give callee functions temporary access
to memory location.

The simplest kind of references are `&T`
which denote _read-only_ access to a value
of type `T`. For example, we might write `abs` to take
a shared reference to an `i32`

```rust, editable
#[flux_rs::spec(fn (p: &i32[@n]) -> i32{v:0<=v && n<=v})]
pub fn abs(p: &i32) -> i32 {
    let n = *p;
    if 0 <= n {
        n
    } else {
        0 - n
    }
}
```

Notice that the _input_ type has changed. Now, the function

- **accepts** `p`, a _reference_ to an `i32` whose value is `n` as denoted by `@n`
- **returns** an `i32` that is non-negative and larger than `n`

The `@` marks the `n` as a _refinement parameter_ whose value
is automatically computed by flux during type checking.

<!-- SLIDE -->

### Calling `abs` with a reference

So, for example, Flux can check the below code by automatically
determining that the refinement parameter at the call-site is `10`.

```rust, editable
pub fn test_abs() {
    let z = 10;
    assert(0 <= abs(&z));
    assert(10 <= abs(&z))
}
```

<!-- SLIDE -->

### Refinement Parameters

As an aside, we have secretly been using _refinement parameters_
like `@n` all along. For example, Flux automatically _desugars_
the signature `fn(n:i32{0 <= n} -> ...` that we wrote for `factorial` into

```
fn ({i32[@n] : 0 <= n}) -> i32{v:n <= v}
```

where `@n` is a refinement parameter that is _implicitly_ determined
from the rust parameter `n:i32`. However, _explicit_ parameters are
essential to _name_ the value of what a reference points to.
In `abs` the `rust` parameter `p` names the reference but the
`@n` names the (input) _value_ and lets us use it to provide
more information about the output of `abs`.

**EXERCISE** Flux is _modular_ in that the
_only_ information it knows about the
implementation of `abs` is the signature.
For example, suppose we change the output type
of `abs` to `i32{v:0<=v}`, that is, we remove the
`n <= v` conjunct. Can you predict which `assert`
will be rejected by flux?

<!-- SLIDE -->

## Borrowing: Mutable References

References of type `&mut T` denote _mutable_ references that can be
used to (read and) write or update the contents of a `T` value.
Crucially, Rust ensures that while there may be multiple read-only (shared)
references to a location, there is at most one _active_ writeable (mutable)
reference at any point in time.

Flux exploits the semantics of `&mut T` to treat `T` as an _invariant_
of the underlying data. As an example, consider the following function
that _decrements_ the value of a mutable reference while ensuring the
data is non-negative:

```rust, editable
#[flux_rs::spec(fn(p: &mut i32{v:0 <= v}))]
pub fn decr(p: &mut i32) {
    *p = *p - 1;
}
```

Flux complains that

```
error[FLUX]: assignment might be unsafe
   |
13 |         *p = *p - 1;
   |         ^^^^^^^^^^^
```

as in fact, we _may_ be writing a negative value into `*p`
for example, if the old value was zero. We can fix this
code by guarding the update with a test that ensures the
original contents are in fact _non-zero_

**EXERCISE** Can you _modify_ the code for `decr` so that flux verifies it?

<!-- SLIDE -->

### Aliased References

Flux uses Rust's borrowing rules to track invariants even when
there may be aliasing. As an example, consider the function

```rust, editable
#[flux_rs::spec(fn (bool) -> i32{v:0 <= v})]
fn test_alias(z: bool) -> i32 {
    let mut x = 1;  // x: i32[1]
    let mut y = 2;  // y: i32[2]
    let r = if z { &mut x } else { &mut y };
                    // r: &mut i32{v:0 <= v}
    decr(r);
    *r
}
```

The reference `r` could point to _either_ `x` or `y` depending
on the (unknown) value of the boolean `z`. Nevertheless, Flux
determines that _both_ references `&mut x` and `&mut y` point
to values of the more general type `i32{v:0<=v}` and hence,
infers `r : &mut i32{v:0<=v}` which allows us it to then call
`decr` with the reference and guarantee the result (after `decr`)
is still non-negative.

<!-- SLIDE -->

### Invariants are not enough!

In many situations, we want to lend a value to another function
that actually _changes_ the value's (refinement) type upon exit.
For example, consider the following function to _increment_
a reference to a non-negative `i32`

```rust, editable
#[flux_rs::spec(fn (p: &mut i32{v:0 <= v}))]
fn incr_inv(p: &mut i32) {
  *p += 1
}

fn test_incr_inv() {
  let mut z = 10;
  incr_inv(&mut z);
  assert(z == 11);
}
```

The only information that `flux` has about `incr` what
it says in its `spec`, namely, that `p` remains non-negative.
Flux is blissfully unaware that `incr` _increments_
the value of `p`, and it cannot prove that after the
call, `z == 11` and hence, complains that `assert`
may fail even though it will obviously succeed!

<!-- SLIDE -->

## Borrowing: _Updatable_ References

To verify `test_incr` we need a signature for `incr` that says
that its _output_ is indeed one greater[^2] than its input.

Flux extends Rust `&mut T` with the notion of **updatable references**
which _additionally_ specify how the type is _changed_ when
the function exits[^3], using an `ensures` clause that specifies
the _modified_ type of the reference.

```rust, editable
#[flux_rs::spec(fn(p: &mut i32[@n]) ensures p:i32[n+1])]
fn incr(p: &mut i32) {
  *p += 1
}
```

The Flux signature refines the plain Rust one to specify that

1. `p` is a strong reference to an `i32`,
2. the _input type_ of `*p` is `i32[n]`, and
3. the _output type_ of `*p` is `i32[n+1]`.

With this specification, Flux merrily checks `test_incr`, by
determining that the refinement parameter `@n` is `10` and
hence, that upon return `x: i32[11]`.

```rust, editable
fn test_incr() {
  let mut z = 10;
  incr_inv(&mut z);
  assert(z == 11);
}
```

<!-- SLIDE -->

## Summary

To sum up, Flux exploits Rust's ownership mechanisms
to track properties of _shared_ (`&T`) and _mutable_
(`&mut T`) references, and additionally uses (`ensures`)
clauses to specify when the type itself is _changed_ by a call.

[^1]: For those familiar with the term, these types are _loop invariants_

[^2]: Setting aside the issue of overflows for now

[^3]: Thereby allowing so-called _strong updates_ in the type specifications
