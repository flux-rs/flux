# Refining Structs

```rust, editable, hidden
#![allow(unused)]
extern crate flux_rs;
use flux_rs::attrs::*;

#[flux_rs::spec(fn (bool[true]))]
fn assert(b: bool) {
    if !b {
        panic!("assertion failed");
    }
}
```

Previously, we saw how to slap refinements on existing _built-in_
or _primitive_ Rust types. For example,

- `i32[10]` specifies the `i32` that is _exactly_ equal to `10` and
- `i32{v: 0 <= v && v < 10}` specifies an `i32` between `0` and `10`.

Next, lets see how to attach refinements to _user-defined_ types,
so we can precisely define the set of _legal_ values of those types.

<!-- SLIDE -->

## Positive Integers

Lets start with an example posted on the [flux gitHub](https://github.com/flux-rs/flux/issues/1106):

> how do you create a Positivei32? I can think of two ways: `struct Positivei32 { val: i32, }` and struct `Positivei32(i32);` but I do not know how to apply the refinements for them. I want it to be an invariant that the i32 value is >= 0. How would I do this?

With flux, you can define the `Positivei32` type as follows:

```rust, editable
#[refined_by(n: int)]
#[invariant(n > 0)]
struct Positivei32 {
  #[field(i32[n])]
  val: i32
}
```

In addition to defining the plain Rust type `Positivei32`,
the flux refinements say _three_ distinct things.

1. The `refined_by(n: int)` tells flux to refine each
   `Positivei32` with a special `int`-sorted _index_ named `n`,
2. the `invariant(n > 0)` says that the index `n`
   is always positive, and,
3. the `field` attribute on `val` says that the
   type of the field `val` is an `i32[n]`
   i.e. is an `i32` whose exact value is `n`.

<!-- SLIDE -->

### Creating Positive Integers

Now, you would create a `Positivei32` pretty much as you might in Rust:

```rust, editable
#[spec(fn() -> Positivei32)]
fn mk_positive_1() -> Positivei32 {
  Positivei32 { val: 1 }
}
```

and flux will prevent you from creating an _illegal_ `Positivei32`, like

```rust, editable
#[spec(fn() -> Positivei32)]
fn mk_positive_0() -> Positivei32 {
  Positivei32 { val: 0 }
}
```

<!-- SLIDE -->

### A Constructor

**EXERCISE** Consider the following `new` constructor for `Positivei32`. Why does flux reject it?
Can you figure out how to fix the `spec` for the constructor so flux will be appeased?

```rust, editable
impl Positivei32 {
  pub fn new(val: i32) -> Self {
    Positivei32 { val }
  }
}
```

<!-- SLIDE -->

### A "Smart" Constructor

**EXERCISE** Here is a different, constructor that should work
for _any_ input `n` but which may return `None` if the input is
invalid. Can you fix the code so that flux accepts `new_opt`?

```rust, editable
impl Positivei32 {
  pub fn new_opt(val: i32) -> Option<Self> {
      Some(Positivei32 { val })
  }
}
```

<!-- SLIDE -->

### Tracking the Field Value

In addition to letting us constrain the underlying `i32` to be positive,
the `n: int` index lets flux precisely _track_ the value of the `Positivei32`.
For example, we can say that the following function returns a very specific `Positivei32`:

```rust, editable
#[spec(fn() -> Positivei32[{n:10}])]
fn mk_positive_10() -> Positivei32 {
  Positivei32 { val: 10 }
}
```

(When there is a single index, we can just write `Positivei32[10]`.)

Since the field `val` corresponds to the _tracked index_,
flux "knows" what `val` is from the index, and hence lets us check that

```rust, editable
#[spec(fn() -> i32[10])]
fn test_ten() -> i32 {
    let p = mk_positive_10(); // p   : Positivei32[{n: 10}]
    let res = p.val;          // res : i32[10]
    res
}
```

<!-- SLIDE -->

### Tracking the Value in the Constructor

**EXERCISE** Scroll back up, and modify the `spec` for `new`
so that the below code verifies. That is, modify the `spec`
so that it says what the value of `val` is when `new` returns
a `Positivei32`. You will likely need to _combine_ indexes
and constraints as shown in [the example `add_points`](./01-refinements.md#combining-indexes-and-constraints).

```rust, editable
#[spec(fn() -> i32[99])]
fn test_new() -> i32 {
    let p = Positivei32::new(99);
    let res = p.val;
    res
}
```

<!-- SLIDE -->

### Field vs. Index?

At this point, you might be wondering why, since `n` is the value of the field `val`,
we didn't just name the index `val` instead of `n`?

Indeed, we could have named it `val`.

However, we picked a different name to emphasize that the index is _distinct from_
the field. The field actually exists at run-time, but in contrast, the index is a
_type-level property_ that only lives at compile-time.

<!-- SLIDE -->

## Integers in a Range

Of course, once we can index and constrain a single field, we can do so for many fields.

For instance, suppose we wanted to write a `Range` type with two fields `start` and `end`
which are integers such that `start <= end`. We might do so as

```rust, editable
#[refined_by(start: int, end: int)]
#[invariant(start <= end)]
struct Range {
  #[field(i32[start])]
  start: i32,
  #[field(i32[end])]
  end: i32,
}
```

Note that this time around, we're using the _same names_ for the index as the field
names (even though they are conceptually distinct things).

<!-- SLIDE -->

### Legal Ranges

Again, the refined `struct` specification will ensure we only create legal `Range` values.

```rust, editable
fn test_range() {
    vec![
        Range { start: 0, end: 10 }, // ok
        Range { start: 15, end: 5 }, // rejected!
    ];
}
```

<!-- SLIDE -->

### A Range Constructor

**EXERCISE** Fix the specification of the `new`
constructor for `Range` so that both `new` and
`test_range_new` are accepted by flux. (Again,
you will need to _combine_ indexes and constraints
as shown in [the example `add_points`](./01-refinements.md#combining-indexes-and-constraints).)

```rust, editable
impl Range {
    pub fn new(start: i32, end: i32) -> Self {
        Range { start, end }
    }
}

#[spec(fn() -> Range[{start: 0, end: 10}])]
fn test_range_new() -> Range {
    let rng = Range::new(0, 10);
    assert(rng.start == 0);
    assert(rng.end == 10);
    rng
}
```

<!-- SLIDE -->

### Combining Ranges

Lets write a function that computes the _union_ of two ranges.
For example, given the range from `10-20` and `15-25`, we might
want to return the the union is `10-25`.

```rust, editable
fn min(x:i32, y:i32) -> i32 {
  if x < y { x } else { y }
}

fn max(x:i32, y:i32) -> i32 {
  if x < y { y } else { x }
}

fn union(r1: Range, r2: Range) -> Range {
  let start = min(r1.start, r2.start);
  let end = max(r2.end, r2.end);
  Range { start, end }
}
```

**EXERCISE** Can you figure out how to fix the `spec` for `min` and `max`
so that flux will accept that `union` only constructs legal `Range` values?

<!-- SLIDE -->

## Refinement Functions

When _code_ get's more complicated, we like to abstract it into reusable
functions. Flux lets us do the same for refinements too. For example, we
can define refinement-level functions `min` and `max` which take `int`
(not `i32` or `usize` but logical `int`) as input and return that as output.

```rust, editable
defs! {
    fn min(x: int, y: int) -> int {
        if x < y { x } else { y }
    }
    fn max(x: int, y: int) -> int {
        if x < y { y } else { x }
    }
}
```

We can now use refinement functions like `min` and `max` inside types.
For example, the output type of `decr` precisely tracks the decremented value.

```rust, editable
impl Positivei32 {
  #[spec(fn(&Self[@p]) -> Self[max(1, p.n - 1)])]
  fn decr(&self) -> Self {
    let val = if self.val > 1 { self.val - 1 } else { self.val };
    Positivei32 { val }
  }
}

fn test_decr() {
  let p = Positivei32{val: 2}; // p : Positivei32[2]
  assert(p.val == 2);
  let p = p.decr();            // p : Positivei32[1]
  assert(p.val == 1);
  let p = p.decr();            // p : Positivei32[1]
  assert(p.val == 1);
}
```

<!-- SLIDE -->

### Combining Ranges, Precisely

**EXERCISE** The `union` function that we wrote
above says _some_ `Range` is returned, but nothing
about _what_ that range actually is! Fix the `spec`
for `union` below, so that flux accepts `test_union` below.

```rust, editable
impl Range {
  #[spec(fn(&Self[@r1], &Self[@r2]) -> Self)]
  pub fn union(&self, other: &Range) -> Range {
    let start = if self.start < other.start {
        self.start
    } else {
        other.start
    };
    let end = if self.end < other.end {
        other.end
    } else {
        self.end
    };
    Range { start, end }
  }
}

fn test_union() {
  let r1 = Range { start: 10, end: 20 };
  let r2 = Range { start: 15, end: 25 };
  let r3 = r1.union(&r2);
  assert(r3.start == 10);
  assert(r3.end == 25);
}
```

## Summary

To conclude, we saw how you can use flux to refine user-defined `struct` to track,
at the type-level, the values of fields, and to then constrain the sets of _legal_
values for those structs.

To see a more entertaining example, [check out this code][flux-date-test]
which shows how we can use refinements to ensure that only legal `Date`s can be constructed
at compile time!

[flux-date-test]: https://github.com/flux-rs/flux/blob/f200714dfae5e7c9a3bdf7231191499f56aac45b/tests/tests/pos/surface/date.rs
