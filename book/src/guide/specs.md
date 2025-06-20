# Flux Specification Guide

This is a WIP guide to writing specifications in `flux`.

## Refinement Types

- **Indexed Type**: An indexed type `B[r]` is composed of a base Rust type `B` and a refinement index `r`. The meaning of the index depends on the type. Some examples are

  - `i32[n]`: denotes the (singleton) set of `i32` values equal to `n`.
  - `List<T>[n]`: values of type `List<T>` of length `n`.

- **Refinement parameter**: Function signatures can be parametric on refinement variables. Refinement parameters are declared using the `@n` syntax. For example, the following signature:

  `fn(i32[@n]) -> i32[n + 1]`

  binds `n` over the entire scope of the function to specify that it takes an `i32` equal to `n` and returns an `i32` equal to `n + 1`. This is analogous to languages like Haskell where a lower case letter can be used to quantify over a type, e.g., the type `a -> a` in Haskell is polymorphic on the type `a` which is bound for the scope of the entire function type.

- **Existential Type**: An existential type `B{v: r(v)}` is composed of a base type `B`, a refinement variable `v` and a refinement predicate `r` on `v`. Intuitively, a Rust value `x` has type `B{v: r(v)}` if there exists a refinement value `a` such that `r(a)` holds and `x` has type `B[a]`.

  - `i32{v: v > 0}`: set of positive `i32` values.
  - `List<T>{v: v > 0}`: set of non-empty lists.

- **Constraint Type**: A constraint type has the form `{T | r}` where `T` is any type (not just a base type). Intuitively, a value has type `{T | r}` if it has type `T` and also `r` holds. They can be used to constraint a refinement parameter. For example, the following signature constraint the refinement parameter `n` to be less than `10`.

  `fn({i32[@n] | n < 10}) -> i32[n + 1]`

  Constraint types serve a similar role as existentials as they can also be used to constraint some
  refinement value with a predicate, but an existential type can only be used to constraint refinement
  variable that it bound locally, in contrast constraint types can be used to constraint a "non-local" parameter. This can be seen in the example above where the parameter `n` cannot be bound locally
  because it has to be used in the return type.

## Argument Syntax

The `@n` syntax used to declare refinements parameters can be hard to read sometimes. Flux also supports a syntax that let you bind refinement parameters using colons similar to the syntax used to declare arguments in a function. We call this _argument syntax_. This syntax desugars to one of the refinements forms discussed above. For example, the following signature

`fn(x: i32, y: i32) -> i32[x + y]`

desugars to

`fn(i32[@x], i32[@y]) -> i32[x + y]`

It is also possible to attach some constraint to the parameters when using argument syntax. For example,
to specify that `y` must be greater than `x` using argument syntax we can write:

`fn(x: i32, y: i32{x > y}) -> i32[x + y]`

This will desugar to:

`fn(i32[@x], {i32[@y] | x > y}) -> i32[x + y]`

## Extern specs

Sometimes you may want to refine a struct or function that outside your code. We
refer to such a specification as an "extern spec," which is short for "external
specification."

Currently, Flux supports extern specs for functions, structs, enums, traits and impls.
The support is a bit rudimentary. For example, multiple impls for a struct (such as `&[T]`
and `[T]`) may conflict, and extern specs for structs only support opaque refinements.

Extern specs are given using `extern_spec` attribute macro, which is provided
by the procedural macros package `flux_rs`.

```
use flux_rs::extern_spec;
```

### Extern functions

An example of refining an extern function can be found
[here](https://github.com/flux-rs/flux/blob/d49a74dc59b2b9bb1dda01ee019d0ab9a66cdd89/flux-tests/tests/pos/surface/extern_spec_macro.rs).

To define an extern spec on a function, you need to do three things, which
happen to correspond to each of the below lines.

```rust
{{#include ../../../tests/tests/neg/surface/extern_spec_swap.rs:5:7}}
```

1. Add the `#[extern_spec]` attribute. This attribute optionally takes a path;
   in the above example, this is `std::mem`. You can use this path to qualify
   the function. So in the above example, the function we are targeting has the
   full path of `std::mem::swap`.
2. Add a `#[spec(...)]` (or equivalently `#[flux_rs::sig(...)]`) attribute, which
   is required for any extern spec on a function. This signature behaves as if
   the `#[flux_rs::trusted]` attribute was added, because we cannot _actually_
   check the implementation. Instead, flux just verifies some simple things,
   like that the function arguments have compatible types.
3. Write a function stub whose rust signature matches the external function.

If you do the above, you can use `std::mem::swap` as if it were refined by the
above type.


```rust
{{#include ../../../tests/tests/neg/surface/extern_spec_swap.rs:9:16}}
```

You shouldn't need to know the details, but if you're curious,
here's how the macro works. In the code above, flux parses the
`std::mem` into a module path and then transforms the function into

```rust
#[extern_spec]
#[spec(fn(x: &mut T[@vx], y: &mut T[@vy]) ensures x: T[vy], y: T[vx])]
#[allow(unused, dead_code)]
fn __flux_extern_spec_swap<T>(x: &mut T, y: &mut T) {
    std::mem::swap(x, y)
}
```

It does this to get information about the function `std::mem::swap` and its
arguments (this turns out to be difficult to do without giving the compiler
something to inspect and type check).

### Extern `struct` and `impl`

Here is an example of refining an extern struct

```rust
{{#include ../../../tests/tests/neg/extern_specs/extern_spec_struct.rs}}
```

Here's a longer example of refining an extern `struct` as well as an `impl`

```rust
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_impl00.rs}}
```

The syntax for an extern spec on a struct is very similar to that for a
function. Once again, each line in the example happens to correspond to a step.

```
#[extern_spec(std::string)]
#[flux_rs::refined_by(len: int)]
struct String;
```

1. Add the `#[extern_spec]` attribute. This attribute optionally takes a path;
   in the above example, this is `std::string`. You can use this path to qualify
   the function. So in the above example, the struct we are targeting has the
   full path of `std::string::String`.
2. Add a `#[flux_rs::refined_by(...)]` attribute. This is required for any extern
   spec on a struct. Right now these attributes behave as if they were opaque
   (`#[flux_rs::opaque]`), although we may support non-opaque extern structs.
3. Write a stub for the extern struct.

If you do the above, you can use `std::string::String` as if it were refined by
an integer index.

The syntax for an extern impl is a little different than that for functions or
structs.

```
#[extern_spec(std::string)]
impl String {
    #[flux_rs::sig(fn() -> String[0])]
    fn new() -> String;

    #[flux_rs::sig(fn(&String[@n]) -> usize[n])]
    fn len(s: &String) -> usize;
}
```

1. You still need to add the `#[extern_spec]` attribute, with the same optional
   argument of the path as above.
2. You need to write out the `impl` block for the struct you want to refine.
   This struct does not need an extern spec, since by refining the `impl` you're
   only refining its methods.
3. Write an extern spec for each function you wish to refine (this may be a
   subset). This is written just like a function extern spec with the caveat
   that the `self` parameter is not presently supported. So for example, instead
   of writing `fn len(&self) -> usize;`, you need to write `fn len(s: &String)
-> usize;`.

If you do the above, you can use the above methods of`std::string::String` as if
they were refined.

## Grammar of Refinements

```text
r ::= n                     // numbers 1,2,3...
    | x                     // identifiers x,y,z...
    | x.f                   // index-field access
    | r + r                 // addition
    | r - r                 // subtraction
    | n * e                 // multiplication by constant
    | if r { r } else { r } // if-then-else
    | f(r...)               // function application
    | true | false          // booleans
    | r == r                // equality
    | r != r                // not equal
    | r < r                 // less than
    | r <= r                // less than or equal
    | r > r                 // greater than
    | r >= r                // greater than or equal
    | r || r                // disjunction
    | r && r                // conjunction
    | r => r                // implication
    | !r                    // negation
```

## Ignored and trusted code

Flux offers two attributes for controlling which parts of your code it analyzes: `#[flux_rs::ignore]` and `#[flux_rs::trusted]`.

- `#[flux_rs::ignore]`: This attribute is applicable to any item, and it instructs Flux to completely skip some code. Flux won't even look at it.
- `#[flux_rs::trusted]`: This attribute affects whether Flux checks the body of a function. If a function is marked as trusted, Flux won't verify its body against its signature. However, it will still be able to reason about its signature when used elsewhere.

The above means that an _ignored_ function can only be called from ignored or trusted code, while a _trusted_ function can also be called from analyzed code.

Both attributes apply recursively. For instance, if a module is marked as `#[flux_rs::ignore]`, all its nested elements will also be ignored. This transitive behavior can be disabled by marking an item with `#[flux_rs::ignore(no)]`[^ignore-shorthand], which will include all nested elements for analysis. Similarly,
the action of `#[flux_rs::trusted]` can be reverted using `#[flux_rs::trusted(no)]`.

Consider the following example:

```rust
#[flux_rs::ignore]
mod A {

   #[flux_rs::ignore(no)]
   mod B {
      mod C {
         fn f1() {}
      }
   }

   mod D {
      fn f2() {}
   }

   fn f3() {}
}
```

In this scenario, functions `f2` and `f3` will be ignored, while `f1` will be analyzed.

A typical pattern when retroactively adding Flux annotations to existing code is to ignore an entire crate (using the inner attribute `#![flux_rs::ignore]` at the top of the crate) and then selectively include specific sections for analysis.

[^ignore-shorthand]: `#[flux_rs::ignore]` (resp. `#[flux_rs::trusted]`) is shorthand for `#[flux_rs::ignore(yes)]` (resp. `#[flux_rs::trusted(yes)]`).

## Opaque

Flux offers an attribute `opaque` which can be used on structs. A module defining an opaque struct should define a trusted API, and clients of the API should not access struct fields directly. This is particularly useful in cases where users need to define a type indexed by a different type than the structs fields. For example, `RMap` (see below) defines a refined HashMap, indexed by a `Map` - a primitive sort defined by flux.

```rust
use flux_rs::*;

#[opaque]
#[refined_by(vals: Map<K, V>)]
pub struct RMap<K, V> {
    inner: std::collections::HashMap<K, V>,
}
```

**Note that opaque structs **can not** have refined fields.**

Now, we can define `get` for our refined map as follows:

```rust
#[generics(K as base, V as base)]
impl<K, V> RMap<K, V> {

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&RMap<K, V>[@m], &K[@k]) -> Option<&V[map_select(m.vals, k)]>)]
    pub fn get(&self, k: &K) -> Option<&V>
    where
        K: Eq + Hash,
    {
        self.inner.get(k)
    }

}
```

Note that if we do not mark these methods as `trusted`, we will get an error that looks like...

```rust
error[E0999]: cannot access fields of opaque struct `RMap`.
  --> ../opaque.rs:22:9
   |
22 |         self.inner.get(k)
   |         ^^^^^^^^^^
-Ztrack-diagnostics: created at crates/flux-refineck/src/lib.rs:111:14
   |
help: if you'd like to use fields of `RMap`, try annotating this method with `#[flux::trusted]`
  --> ../opaque.rs:18:5
   |
18 | /     pub fn get(&self, k: &K) -> Option<&V>
19 | |     where
20 | |         K: Eq + std::hash::Hash,
   | |________________________________^
   = note: fields of opaque structs can only be accessed inside trusted code
```
