# Refining Enums

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

[Previously](./03-structs.md) we saw how to refine structs to constrain the space
of legal values, for example, to define a `Positivei32` or a `Range` `struct` where
the `start` was less than or equal to the `end`. Next, lets see how the same mechanism
can be profitably used to let us check properties of `enums` at compile time.

<!-- SLIDE -->

## Failure is an Option

Rust's type system is really terrific for spotting all
manner of bugs at compile time. However, that just makes
it all the more disheartening to get runtime errors like

```
thread ... panicked at ... called `Option::unwrap()` on a `None` value
```

Lets see how to refine `enum`'s like `Option` to
let us `unwrap` without the anxiety of run-time failure.

<!-- SLIDE -->

### A Refined Option

To do so, lets define a custom `Option` type [^1] that
is indexed by a `bool` which indicates whether or not
the option is valid (i.e. `Some` or `None`):

```rust, editable
#[refined_by(valid: bool)]
enum Option<T> {
    #[variant((T) -> Option<T>[{valid: true}])]
    Some(T),
    #[variant(Option<T>[{valid: false}])]
    None,
}
```

As with `std::option::Option`, we have two variants

- `Some`, with the "payload" `T` and
- `None`, without.

However, we have tricked out the type in two ways.

- First, we added a `bool` sorted index that aims to track whether the option is `valid`;
- Second, we used the `variant` attribute to specify the value of the index for the `Some` and `None` cases.

<!-- SLIDE -->

### Constructing Options

The definition above tells flux that `Some(...)`
has the refined type `Option<...>[{valid: true}]`,
and `None` has the refined type `Option<...>[{valid: false}]`.

**NOTE** When there is a _single_ refinement index, we can skip the `{valid:b}`
and just write `b`.

```rust, editable
#[spec(fn () -> Option<i32>[true])]
fn test_some() -> Option<i32> {
  Option::Some(12)
}

#[spec(fn () -> Option<i32>[false])]
fn test_none() -> Option<i32> {
  Option::None
}
```

<!-- SLIDE -->

### Destructing Options by Pattern Matching

The neat thing about refining variants is that _pattern matching_
on the `enum` tells flux what the variant's refinements are.

For example, consider the following implementation of `is_some`

```rust, editable
impl<T> Option<T> {
  #[spec(fn(&Self[@valid]) -> bool[valid])]
  pub fn is_some(&self) -> bool {
    match self {
      Option::Some(_) => true,  // self : &Option<..>[true]
      Option::None => false,    // self : &Option<..>[false]
    }
  }
}
```

<!-- SLIDE -->

### Never Do This!

When working with `Option` types, or more generally,
with `enum`s, we often have situations in pattern-match
cases where we "know" that that case will not arise.

Typically we mark those cases with an `unreachable!()` call.

With flux, we can do even more: we can _prove_, at compile-time,
that those cases will never, in fact, be executed.

```rust, editable
#[spec(fn () -> _ requires false)]
fn unreachable() -> ! {
    assert(false);  // flux will prove this is unreachable
    unreachable!(); // panic if we ever get here
}
```

The _precondition_ `false` ensures that the _only_ way that
a call to `unreachable` can be verified is when flux can prove
that the call-site is "dead code".

```rust, editable
fn test_unreachable(n: usize) {
  let x = 12;           // x : usize[12]
  let x = 12 + n;       // x : usize[12 + n] where 0 <= n
  if x < 12 {
    unreachable();      // impossible, as x >= 12
  }
}
```

<!-- SLIDE -->

### Unwrap Without Anxiety!

Lets use our refined `Option` to implement a safe `unwrap` function.

```rust, editable
impl <T> Option<T> {
  #[spec(fn(Self[true]) -> T)]
  pub fn unwrap(self) -> T {
    match self {
      Option::Some(v) => v,
      Option::None => unreachable(),
    }
  }
}
```

The `spec` requires that `unwrap` is _only_ called
with an `Option` whose (`valid`) index is `true`,
i.e. `Some(...)`.

The `None` pattern is matched only when the index
is `false` which is impossible, as it contradicts
the precondition.

Hence, flux concludes that pattern is dead code
(like the `x < 12` branch is dead code in the
`test_unreachable` above.)

<!-- SLIDE -->

## Using `unwrap`

Next, lets see some examples of how to use refined options
to safely `unwrap`.

<!-- SLIDE -->

### Safe Division

Here's a safe divide-by-zero function that returns an `Option<i32>`:

```rust, editable
#[spec(fn(n:i32, k:i32) -> Option<i32>)]
pub fn safe_divide(n: i32, k: i32) -> Option<i32> {
  if k > 0 {
    Option::Some(n / k)
  } else {
    Option::None
  }
}
```

**EXERCISE** Why does the test below fail to type check?
Can you fix the `spec` for `safe_divide` so flux is happy
with `test_safe_divide`?

```rust, editable
fn test_safe_divide() -> i32 {
    safe_divide(10, 2).unwrap()
}
```

<!-- SLIDE -->

### Smart Constructors Revisited

Recall the [`struct Positivei32`](./03-structs.md#positive-integers)
and the smart constructor we wrote for it.

```rust, editable
#[refined_by(n: int)]
#[invariant(n > 0)]
struct Positivei32 {
    #[field(i32[n])]
    val: i32
}

impl Positivei32 {
  #[spec(fn(val: i32) -> Option<Self>)]
  pub fn new(val: i32) -> Option<Self> {
    if val > 0 {
      Option::Some(Positivei32 { val })
    } else {
      Option::None
    }
  }
}
```

**EXERCISE** The code below has a function that
invokes the smart constructor and then `unwrap`s
the result. Why is flux complaining? Can you fix
the `spec` of `new` so that the `test_unwrap` figure
out how to fix the `spec` of `new` so that `test_new_unwrap`
is accepted?

```rust, editable
fn test_new_unwrap() {
    Positivei32::new(10).unwrap();
}
```

<!-- SLIDE -->

## TypeStates: A Refined Timer

Lets look a different way to use refined `enum`s.
On the [flux zulip][zulip-timer] we were asked
if we could write an `enum` to represent a `Timer`
with two variants:

- `Inactive` indicating that the timer is not running, and
- `CountDown(n)` indicating that the timer is counting down from `n` seconds.

Somehow using refinements to ensure that the timer can only
be set to `Inactive` when `n < 1`.

<!-- SLIDE -->

### Refined Timers

To do so, lets define the `Timer`, refined with an `int` index that tracks
the number of remaining seconds.

```rust, editable
#[flux::refined_by(remaining: int)]
enum Timer {
    #[flux::variant(Timer[0])]
    Inactive,

    #[flux::variant((usize[@n]) -> Timer[n])]
    CountDown(usize)
}
```

The flux definitions ensure that `Timer` has two variants

- `Inactive`, which has a `remaining` index of `0`, and
- `CountDown(n)`, which has a `remaining` index of `n`.

<!-- SLIDE -->

### Timer Implementation

We can now implement the `Timer` with a constructor and a method to set it to `Inactive`.

```rust, editable
impl Timer {
    #[spec(fn (n: usize) -> Timer[n])]
    pub fn new(n: usize) -> Self {
       Timer::CountDown(n)
    }

    #[spec(fn (self: &mut Self[0]))]
    fn deactivate(&mut self) {
        *self = Timer::Inactive
    }
}
```

<!-- SLIDE -->

### Deactivate the Timer

Now, you can see that flux will only let us `set_inactive`
a timer whose countdown is at `0`.

```rust
fn test_deactivate() {
  let mut t0 = Timer::new(0);
  t0.deactivate(); // verifies

  let mut t3 = Timer::new(3);
  t3.deactivate(); // rejected
}
```

<!-- SLIDE -->

### Ticking the Timer

Here is a function to `tick` the timer down by one second.

<!-- // #[spec(fn (self: &mut Self[@s]) ensures self: Self[if n > 1 then n-1 else 0])] -->

```rust, editable
impl Timer {
  #[spec(fn (self: &mut Self[@s]) ensures self: Self)]
  fn tick(&mut self) {
    match self {
      Timer::CountDown(s) => {
        let n = *s;
        if n > 0 {
          *s = n - 1;
        }
      }
      Timer::Inactive => {},
    }
  }
}
```

**EXERCISE** Can you fix the `spec` for `tick` so that flux accepts the following test?

```rust, editable
fn test_tick() {
  let mut t = Timer::new(3);
  t.tick();       // should decrement to 2
  t.tick();       // should decrement to 1
  t.tick();       // should decrement to 0
  t.deactivate(); // should set to Inactive
}
```

## Summary

In this chapter, we saw how you refine an `enum` with indices, and then specify
the values of the indices for each `variant`. This let us, for example, determine
whether an `Option` is `Some` or `None` at compile time, and to safely `unwrap`
the former, and to encode a "typestate" mechanism for a `Timer` that tracks how
many seconds remain in a countdown, ensuring we only `deactivate` when the timer
has expired.

You can do various other fun things, like

- track the [length][flux-list-length] of a linked list or
- track the set of [elements][flux-list-elements] in the list, or
- determine whether an expression is in [normal form](./10-case-study-anf.md), or
- ensure the layers of a [neural network](./12-case-study-neural.md)
  are composed correctly.

[^1]: In the chapter on [extern specifications](06-extern-specs.md) we will explain how to "retrofit" these refinements onto the existing `std::option::Option` type.

[flux-list-length]: https://github.com/flux-rs/flux/blob/main/tests/tests/pos/enums/list00.rs
[flux-list-elements]: https://github.com/flux-rs/flux/blob/main/tests/tests/pos/enums/list01.rs
[zulip-timer]: https://flux-rs.zulipchat.com/#narrow/channel/486098-general/topic/greetings/near/509911720
