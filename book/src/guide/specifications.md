# Flux Specifications

One day, this will be an actual user's guide, but for now,
it is a WIP guide to writing specifications in `flux`, as
illustrated by examples from the regression tests.

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

## Grammar of Refinements

The grammar of refinements (expressions that can appear as an index or constraint) is as follows:

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

## Index Refinements

Of the form `i32[e]` (`i32` equal to `e`) values.

```rust,noplayground,noplayground
{{#include ../../../tests/tests/pos/surface/index00.rs}}
```

**NOTE:** We use the `sig(..)` annotation to specify the refinement type of a function;
you can optionally also add the _name_ of the function as shown for `fn five`.

## Existential Refinements

Of the form `i32{v: 0 <= v}` (non-negative `i32`) values.

```rust,noplayground,noplayground
{{#include ../../../tests/tests/pos/surface/test00.rs}}
```

## Combining Index and Existential Refinements

```rust,noplayground,noplayground
{{#include ../../../tests/tests/pos/surface/loop00.rs:6:}}
```

## Mutable References

```rust,noplayground,noplayground
{{#include ../../../tests/tests/pos/surface/test01.rs:58:61}}
```

```rust,noplayground,noplayground
{{#include ../../../tests/tests/neg/surface/test01.rs:15:19}}
```

## Strong References

Like `&mut T` but which allow _strong updates_ via `ensures` clauses

```rust,noplayground,noplayground
{{#include ../../../tests/tests/pos/surface/test03.rs}}
```

## Mixing Mutable and Strong References

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/local_ptr00.rs}}
```

## Refined Arrays

`flux` supports _refined arrays_ of the form `[i32{v: 0 <= v}; 20]`
denoting arrays of size `20` of non-negative `i32` values.

```rust,noplayground
{{#include ../../../tests/tests/pos/array/array00.rs}}
```

## Refined Vectors `rvec`

`RVec` specification

```rust,noplayground
{{#include ../../../tests/tests/lib/rvec.rs}}
```

`RVec` clients

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/rvec00.rs}}
```

**Binary Search**

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/bsearch.rs}}
```

**Heapsort**

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/heapsort.rs}}
```

## Refined Slices

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/slice00.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/rslice00.rs}}
```

## Refined `Vec`

This uses `extern_spec` which is [described below](#extern-specs).

**Standalone**

```rust,noplayground
{{#include ../../../tests/tests/pos/vec/vec00.rs}}
```

**Associated Refinements** for indexing

```rust,noplayground
{{#include ../../../lib/flux-alloc/src/vec/mod.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/neg/surface/vec02.rs}}
```

## Named Function Signatures

You can also write _named_ function signatures using the `spec`
annotation (instead of the anonymous `sig` annotation).

## Requires Clauses

Used to specify preconditions in a single spot, if needed.

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/test01_where.rs}}
```

## Refining Structs

```rust,noplayground
{{#include ../../../tests/tests/pos/structs/dot01.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/date.rs}}
```

### Invariants on Structs

```rust,noplayground
{{#include ../../../tests/tests/pos/structs/invariant00.rs}}
```

with `const` generics

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/invariant_with_const_generic.rs}}
```

### Opaque Structs

Flux offers an attribute `opaque` which can be used on structs. A module defining an opaque struct should define a trusted API, and clients of the API should not access struct fields directly. This is particularly useful in cases where users need to define a type indexed by a different type than the structs fields. For example, `RMap` (see below) defines a refined HashMap, indexed by a `Map` - a primitive sort defined by flux.

```rust,noplayground
use flux_rs::*;

#[opaque]
#[refined_by(vals: Map<K, V>)]
pub struct RMap<K, V> {
    inner: std::collections::HashMap<K, V>,
}
```

**Note that opaque structs **can not** have refined fields.**

Now, we can define `get` for our refined map as follows:

```rust,noplayground
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

```text
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

Here is an example of how to use the `opaque` attribute:

```rust,noplayground
{{#include ../../../tests/tests/pos/structs/opaque-range.rs}}
```

## Refining Enums

```rust,noplayground
{{#include ../../../tests/tests/pos/enums/opt01.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/enums/pos00.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/enums/list00.rs}}
```

### Invariants on Enums

```rust,noplayground
{{#include ../../../tests/tests/pos/enums/invariant00.rs}}
```

### Reflecting Enums

```rust,noplayground
{{#include ../../../tests/tests/neg/surface/reflect00.rs}}
```

## Field Syntax for Indices

### Structs

```rust,noplayground
{{#include ../../../tests/tests/pos/constructors/test00.rs}}
```

### Enums

```rust,noplayground
{{#include ../../../tests/tests/pos/constructors/test01.rs}}
```

### Updates

```rust,noplayground
{{#include ../../../tests/tests/pos/constructors/test03.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/constructors/test04.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/constructors/test05.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/constructors/test11.rs}}
```

## Const

You can use `int`-ish `const` in refinements e.g.

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/const07.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/const08.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/const10.rs}}
```

## Requires with `forall`

We allow a `forall` on the requires clauses, e.g.

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/forall01.rs}}
```

## Refined Associated Types

```rust,noplayground
{{#include ../../../tests/tests/pos/refined_assoc_type/refined_assoc_type00.rs}}
```

## Ignored and trusted code

Flux offers two attributes for controlling which parts of your code it analyzes: `#[flux_rs::ignore]` and `#[flux_rs::trusted]`.

- `#[flux_rs::ignore]`: This attribute is applicable to any item, and it instructs Flux to completely skip some code. Flux won't even look at it.
- `#[flux_rs::trusted]`: This attribute affects whether Flux checks the body of a function. If a function is marked as trusted, Flux won't verify its body against its signature. However, it will still be able to reason about its signature when used elsewhere.

The above means that an _ignored_ function can only be called from ignored or trusted code, while a _trusted_ function can also be called from analyzed code.

Both attributes apply recursively. For instance, if a module is marked as `#[flux_rs::ignore]`, all its nested elements will also be ignored. This transitive behavior can be disabled by marking an item with `#[flux_rs::ignore(no)]`[^ignore-shorthand], which will include all nested elements for analysis. Similarly,
the action of `#[flux_rs::trusted]` can be reverted using `#[flux_rs::trusted(no)]`.

Consider the following example:

```rust,noplayground
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

Here is an example

```rust,noplayground
{{#include ../../../tests/tests/neg/surface/ignore02.rs}}
```

## Pragma: `should_fail`

Used to tell `flux` to _expect_ a failure when checking a function.

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/should_fail.rs}}
```

## Const Generics

`flux` lets you use Rust's const-generics inside refinements.

**Refining Array Lengths**

```rust,noplayground
{{#include ../../../tests/tests/neg/surface/const04.rs}}
```

**Refining Struct Fields**

```rust,noplayground
{{#include ../../../tests/tests/pos/const_generics/struct_invariant.rs}}
```

**Refining Function Signatures**

```rust,noplayground
{{#include ../../../tests/tests/pos/const_generics/matrix.rs}}
```

## Type Aliases

You can define refined **type aliases** for Rust types.

**Note**

1. They are connected to an underlying Rust type,
2. They may also be parameterized by refinements, e.g. `Lb`
3. There are two different kinds of parametrizations
   - _early_ (`Nat`) and
   - _late_ (`Lb`).

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/alias00.rs}}
```

## Spec Function Definitions

You can define **spec functions** that abstract complicated refinements into refinement-level
functions, which can then be used in refinements.

### Plain Expressions

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/date.rs}}
```

### `let` binders

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/let-exprs00.rs}}
```

### Bounded Quantification

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/bounded_quant00.rs}}
```

### No Cycles!

However, there should be no _cyclic dependencies_ in the function definitions.

```rust,noplayground
{{#include ../../../tests/tests/neg/error_messages/dfn_cycle.rs}}
```

## Uninterpreted Function Declarations

You can also declare _uninterpreted_ functions -- about which `flux` knows nothing
other than the congruence property -- and then use them in refinements. Note that
in this case you have to use a `trusted` annotation for the function (e.g. `is_valid`)
that asserts facts over the uninterpreted function

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/uif00.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/uif01.rs}}
```

## Hiding and Revealing Function Definitions

By default all the function definitions are either _inlined_ or sent to the SMT solver
as `define-fun` (when run with `FLUX_SMT_DEFINE_FUN=1`). Sometimes we want to _hide_ the
definition because reasoning about those functions can kill the solver -- or the function
is super complex and we just want to reason about it via congruence. For that you can

- use the `#[hide]` attribute at the spec function definition, to make the function _uninterpreted_ by default, and
- use the `#[reveal]` attribute at specific Rust function definition, to indicate you
  want to use the actual definition when checking that Rust function.

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/hide00.rs}}
```

## Spec Functions in SMTLIB

By default `flux` inlines all such function definitions.

Monomorphic functions may _optionally_ be encoded
as functions in SMT by using the `FLUX_SMT_DEFINE_FUN=1`
environment variable.

## Type Holes

You can (sometimes!) use `_` in the `flux` signatures to omit the Rust components, e.g.

### Function Signatures

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/type_holes00.rs}}
```

### Structs and Enums

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/type_holes01.rs}}
```

### Type Aliases

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/type_holes02.rs}}
```

### Generic Args

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/const11.rs}}
```

## Closures

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/closure00.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/closure02.rs}}
```

## Function Pointers

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/fndef00.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/fndef01.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/fndef02.rs}}
```

## Traits and Implementations

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/impl00.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/impl01.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/impl02.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/refined_fn_in_trait_01.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/trait-subtyping01.rs}}
```

## Impl Trait

```rust,noplayground
{{#include ../../../tests/tests/pos/impl_trait/impl_trait00.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/impl_trait/impl_trait01.rs}}
```

## Dynamic Trait Objects

```rust,noplayground
{{#include ../../../tests/tests/neg/trait_objects/dyn01.rs}}
```

## Generic Refinements

`flux` supports _generic refinements_ see [this paper for details](https://dl.acm.org/doi/10.1145/3704885)

**Horn Refinements**

```rust,noplayground
{{#include ../../../tests/tests/pos/abstract_refinements/test00.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/abstract_refinements/test01.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/abstract_refinements/test03.rs}}
```

**Hindley Refinements**

TODO

## Bitvector Refinements

### Operators

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/bitvec03.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/bitvec_const02.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/bv_ord.rs}}
```

### Specification functions

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/bitvec05.rs}}
```

### Extensions

```rust,noplayground
{{#include ../../../tests/tests/neg/surface/bitvec02.rs}}
```

### Bitvector Constants

```rust,noplayground
{{#include ../../../tests/tests/neg/surface/bitvec_const00.rs}}
```

## `char` Literals

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/char02.rs}}
```

## `String` Literals

```rust,noplayground
{{#include ../../../tests/tests/neg/surface/str02.rs}}
```

## Extern Specs

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

The `extern_spec` is used to provide `flux` signatures for functions defined in _external_ crates. See the [specifications guide](specs.md) for more details.

### Extern Functions

An example of refining an extern function can be found
[here](https://github.com/flux-rs/flux/blob/d49a74dc59b2b9bb1dda01ee019d0ab9a66cdd89/flux-tests/tests/pos/surface/extern_spec_macro.rs).

To define an extern spec on a function, you need to do three things, which
happen to correspond to each of the below lines.

```rust,noplayground
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

Here are two examples:

```rust,noplayground
{{#include ../../../tests/tests/neg/surface/extern_spec_swap.rs:9:16}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_macro.rs}}
```

### Options

```rust,noplayground
{{#include ../../../lib/flux-core/src/option.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/enums/option00.rs}}
```

### Vec

```rust,noplayground
{{#include ../../../lib/flux-alloc/src/vec/mod.rs}}
```

### Extern Structs

Here is an example of refining an extern struct

```rust,noplayground
{{#include ../../../tests/tests/neg/extern_specs/extern_spec_struct.rs}}
```

Here's a longer example of refining an extern `struct` as well as an `impl`

```rust,noplayground
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

```rust,noplayground
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_struct03.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_impl03.rs}}
```

### Extern Impls

```rust,noplayground
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_impl00.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_impl01.rs}}
```

### Extern Traits

```rust,noplayground
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_trait00.rs}}
```

### `for` loops with range `i..j`

To see how `flux` handles `for i in 0..n` style loops:

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/for_range00.rs}}
```

## Associated Refinements

### Basic

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/assoc_reft01.rs}}
```

### Check Subtyping at Impl

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/trait-subtyping08.rs}}
```

### Default

```rust,noplayground
{{#include ../../../tests/tests/neg/surface/assoc_reft03.rs}}
```

### Use in Extern Spec

```rust,noplayground
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_trait00.rs}}
```

```rust,noplayground
{{#include ../../../lib/flux-alloc/src/vec/mod.rs}}
```

```rust,noplayground
{{#include ../../../lib/flux-core/src/iter/mod.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/iter02.rs}}
```

### Associated Types

```rust,noplayground
{{#include ../../../tests/tests/neg/surface/assoc_reft02.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/assoc_reft04.rs}}
```

### Refined Associated Types

```rust,noplayground
{{#include ../../../tests/tests/pos/refined_assoc_type/refined_assoc_type01.rs}}
```

## Checking Overflows

You can switch on overflow checking

- _globally_ [with a flag](http://localhost:3000/guide/run.html?highlight=cache#flux-flags) or
- _locally_ with an attribute as shown below

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/check_overflow00.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/check_overflow01.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/check_overflow02.rs}}
```

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/check_overflow03.rs}}
```

## Extensible Properties for Primitive Ops

You can provide _properties_ to be used when doing computations with
primitive operations like `<<` or `>>`.

Given a primop `op` with signature `(t1,...,tn) -> t` we define
a refined type for `op` expressed as a [`RuleMatcher`]

```rust,noplayground
op :: (x1: t1, ..., xn: tn) -> { t[op_val[op](x1,...,xn)] | op_rel[x1,...,xn] }
```

that is, using two _uninterpreted functions_ `op_val` and `op_rel` that respectively denote

1. The _value_ of the primop, and
2. Some invariant _relation_ that holds for the primop.

The latter can be extended by the user via a `property` definition,
which allows us to customize primops like `<<` with extra "facts"
or lemmas. See `tests/tests/pos/surface/primops00.rs` for an example.

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/primops00.rs}}
```

## Casting Sorts

You can convert refinements of different sorts -- e.g. `int` to `char` or `int` to `bool` --
using the `cast` internal function.

```rust,noplayground
{{#include ../../../tests/tests/pos/surface/to_int00.rs}}
```

## Detached Specifications

Sometimes you may want to write specs for functions etc. but not _directly_ attached to the function
i.e. as an attribute of the function, for example, because you don't want to modify the original source file.

You can do this using the "detached" `spec` as illustrated by the following

```rust,noplayground
{{#include ../../../tests/tests/neg/detached/detach00.rs}}
```

## Include Patterns

You can include patterns to restrict `flux` to only check a subset of a codebase.
A `def_id` is checked if it matches any of the patterns.

```
cargo x run tests/tests/pos/detached/detach00.rs -- -Fdump-checker-trace -Fdump-constraint -Finclude=span:tests/tests/pos/detached/detach00.rs:13:1 -Finclude=def:id -Finclude=path/to/file.rs
```
