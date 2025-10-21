# Refining Types

Types bring order to code. For example, if a variable `i:usize`
then we know `i` is a number that can be used to index a vector.
Similarly, if `v: Vec<&str>` then we can be sure that `v` is a
collection of strings which may _be_ indexed but of course,
not used _as_ an index. However, by itself `usize` doesn't
tell us how big or small the number and hence the programmer
must still rely on their own wits, a lot of tests, and a dash
of optimism, to ensure that all the different bits fit properly
at run-time.

[Refinements][jhala-vazou] are a promising new way to extend
type checkers with logical constraints that _specify_ additional
correctness requirements that can be _verified_ by the compiler,
thereby entirely eliminating various classes of run-time problems.

To begin, let's see how flux lets you refine _basic_ or _primitive_
types like `i32` or `usize` or `bool` with logical constraints that
can be checked at compile time.

<!-- more -->

<!-- SLIDE -->

## Indexed Types

The simplest kind of refinement type in flux is a type that is
_indexed_ by a logical value. For example

| **Type**     | **Meaning**                                          |
| :----------- | :--------------------------------------------------- |
| `i32[10]`    | The (singleton) set of `i32` values equal to `10`    |
| `bool[true]` | The (singleton) set of `bool` values equal to `true` |

<!-- SLIDE -->

### Flux Specifications

First off, we need to add some incantations that pull in the mechanisms
for writing flux specifications as Rust _attributes_.

```rust,editable
#![allow(unused)]
extern crate flux_rs;
use flux_rs::attrs::*;
```

<!-- SLIDE -->

### Post-Conditions

We can already start using these indexed types to start writing (and checking)
code. For example, we can write the following specification which says that
the value _returned_ by `mk_ten` must in fact be `10`

```rust,editable
#[spec(fn() -> i32[10])]
pub fn mk_ten() -> i32 {
    5 + 4
}
```

**Push Play**
Push the "run" button in the pane above. You will see a red squiggle that
and when you hover over the squiggle you will see an error message

```bash
error[...]: refinement type error
  |
7 |     5 + 4
  |     ^^^^^ a postcondition cannot be proved
```

which says that that the _postcondition might not hold_ which means
that the _output_ produced by `mk_ten` may not in fact be an `i32[10]`
as indeed, in this case, the result is `9`! You can eliminate the error
by _editing_ the body to `5 + 4 + 1` or `5 + 5` or just `10`.

<!-- SLIDE -->

### Pre-Conditions

You can use an index to _restrict the inputs_ that a function expects
to be called with.

```rust,editable
#[spec(fn (b:bool[true]))]
pub fn assert(b:bool) {
  if !b { panic!("assertion failed") }
}
```

The specification for `assert` says you can _only_ call
it with `true` as the input. So if you write

```rust,editable
fn test(){
  assert(2 + 2 == 4);
  assert(2 + 2 == 5); // fails to type check
}
```

then `flux` will complain that

```bash
error[FLUX]: precondition might not hold
   |
12 |     assert(2 + 2 == 5); // fails to type check
   |     ^^^^^^^^^^^^^^^^^^
```

meaning at the second call to `assert` the input _may not_
be `true`, as of course, in this case, it is not!

Can you edit the code of `test` to fix the error?

<!-- SLIDE -->

## Index Parameters and Expressions

Its not terribly exciting to only talk about _fixed_ values
like `10` or `true`. To be more useful, `flux` lets you index
types by refinement _parameters_. For example, you can write

```rust,editable
#[spec(fn(n:i32) -> bool[0 < n])]
pub fn is_pos(n: i32) -> bool {
  if 0 < n {
    true
  } else {
    false
  }
}
```

Here, the type says that `is_pos`

- **takes** as _input_ some `i32` _indexed by_ `n`
- **returns** as _output_ the `bool` _indexed by_ `0 < n`

That is, `is_pos` returns `true` _exactly when_ `0 < n`.

We might use this function to check that:

```rust,editable
pub fn test_pos(n: i32) {
  let m = if is_pos(n) { n - 1 } else { 0 };
  assert(0 <= m);
}
```

<!-- SLIDE -->

## Existential Types

Often we don't care about the _exact_ value of a thing -- but just
care about some _properties_ that it may have. For example, we don't
care that an `i32` is equal to `5` or `10` or `n` but that it is
non-negative.

| **Type**         | **Meaning**                                          |
| :--------------- | :--------------------------------------------------- |
| `i32{v: 0 <  v}` | The set of `i32` values that positive                |
| `i32{v: n <= v}` | The set of `i32` values greater than or equal to `n` |

Flux allows such specifications by pairing plain Rust types
with _assertions_ [^1] that constrain the value.

<!-- SLIDE -->

## Existential Output Types

For example, we can rewrite `mk_10` with the output type
`i32{v:0<v}` that specifies a weaker property:
the value returned by `mk_ten_pos` is positive.

```rust,editable
#[spec(fn() -> i32{v: 0 < v})]
pub fn mk_ten_pos() -> i32 {
    5 + 5
}
```

<!-- SLIDE -->

## Example: `abs`olute value

Similarly, you might specify that a function that computes the _absolute_
value of an `i32` with a type which says the result is non-negative _and_
exceeds the input `n`.

```rust,editable
#[spec(fn (n:i32) -> i32{v:0<=v && n<=v})]
pub fn abs(n: i32) -> i32 {
    if 0 <= n {
        n
    } else {
        0 - n
    }
}
```

<!-- SLIDE -->

## Combining Indexes and Constraints

Sometimes, we want to _combine_ indexes and constraints in a specification.

For example, suppose we have some code that manipulates
_scores_ which are required to be between `0` and `100`.
Now, suppose we want to write a function that adds `k`
points to a score `s`. We want to specify that

- The _inputs_ `s` and `k` must be non-negative,
- the _inputs_ `s + k <= 100`, and
- The _output_ equals `s + k`

```rust,editable
#[spec(fn ({usize[@s] | s + k <= 100}, k:usize) -> usize[s + k])]
fn add_points(s: usize, k: usize) -> usize {
    s + k
}

fn test_add_points() {
    assert(add_points(20, 30) == 50);
    assert(add_points(90, 30) == 120); // fails to type check
}
```

Note that we use the `@s` to _index_ the value of the `s` parameter,
so that we can

1. _constrain_ the inputs to `s + k <= 100`, and
2. _refine_ the value of the output to be exactly `usize[s + k]`.

**EXERCISE** Why does flux reject the second call to `add_points`?

<!-- SLIDE -->

## Example: `factorial`

As a last example, you might write a function to compute the factorial of `n`

```rust,editable
#[spec(fn (n:i32) -> i32{v:1<=v && n<=v})]
pub fn factorial(n: i32) -> i32 {
    let mut i = 0;
    let mut res = 1;
    while i < n {
        i += 1;
        res = res * i;
    }
    res
}
```

Here the specification says the input must be non-negative, and the
output is at least as large as the input. Note, that unlike the previous
examples, here we're actually _changing_ the values of `i` and `res`.

<!-- SLIDE -->

## Summary

In this post, we saw how Flux lets you

1. _decorate_ basic Rust types like `i32` and `bool` with
   **indices** and **constraints** that let you respectively
   _refine_ the sets of values that inhabit that type, and

2. _specify_ contracts on functions that state **pre-conditions** on
   the sets of legal inputs that they accept, and **post-conditions**
   that describe the outputs that they produce.

The whole point of Rust, of course, is to allow for efficient _imperative_
sharing and updates, without sacrificing thread- or memory-safety. Next time,
we'll see how Flux melds refinements and Rust's ownership to make refinements
happily coexist with imperative code.

[flux-grammar]: https://github.com/flux-rs/flux/blob/main/book/src/guide/specs.md#grammar-of-refinements
[jhala-vazou]: https://arxiv.org/abs/2010.07763
[flux-github]: https://github.com/liquid-rust/flux/

[^1]: These are not arbitrary Rust expressions but a subset of expressions from logics that can be efficiently decided by [SMT Solvers][flux-grammar]
