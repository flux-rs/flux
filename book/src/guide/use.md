# User's Guide

A list of various `flux` features as illustrated by examples in the regression tests.

## Index Refinements

Of the form `i32[e]` (`i32` equal to `e`) values.

```rust
{{#include ../../../tests/tests/pos/surface/index00.rs}}
```

**NOTE:** We use the `sig(..)` annotation to specify the refinement type of a function;
you can optionally also add the _name_ of the function as shown for `fn five`.

## Existential Refinements

Of the form `i32{v: 0 <= v}` (non-negative `i32`) values.

```rust
{{#include ../../../tests/tests/pos/surface/test00.rs}}
```

## Combining Index and Existential Refinements

```rust
{{#include ../../../tests/tests/pos/surface/loop00.rs:6:}}
```

## Mutable References

```rust
{{#include ../../../tests/tests/pos/surface/test01.rs:58:61}}
```

```rust
{{#include ../../../tests/tests/neg/surface/test01.rs:15:19}}
```

## Strong References

Like `&mut T` but which allow _strong updates_ via `ensures` clauses

```rust
{{#include ../../../tests/tests/pos/surface/test03.rs}}
```

## Refined Vectors `rvec`

`RVec` specification

```rust
{{#include ../../../tests/tests/lib/rvec.rs}}
```

`RVec` clients

```rust
{{#include ../../../tests/tests/pos/surface/rvec00.rs}}
```

**Binary Search**

```rust
{{#include ../../../tests/tests/pos/surface/bsearch.rs}}
```

**Heapsort**

```rust
{{#include ../../../tests/tests/pos/surface/heapsort.rs}}
```

## Named Function Signatures

You can also write _named_ function signatures using the `spec`
annotation (instead of the anonymous `sig` annotation).

## Requires Clauses

Used to specify preconditions in a single spot, if needed.

```rust
{{#include ../../../tests/tests/pos/surface/test01_where.rs}}
```

## Requires with `forall`

We allow a `forall` on the requires clauses, e.g.

```rust
{{#include ../../../tests/tests/pos/surface/forall01.rs}}
```

## Pragma: `ignore`

Used to tell `flux` to _ignore_ (checking) a bunch of definitions.

```rust
{{#include ../../../tests/tests/neg/surface/ignore02.rs}}
```

## Const Generics

`flux` lets you use Rust's const-generics inside refinements.

**Refining Struct Fields**

```rust
{{#include ../../../tests/tests/pos/const_generics/struct_invariant.rs}}
```

**Refining Function Signatures**

```rust
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

```rust
{{#include ../../../tests/tests/pos/surface/alias00.rs}}
```

## Spec Function Definitions

You can define **spec functions** that abstract complicated refinements into refinement-level
functions, which can then be used in refinements.

```rust
{{#include ../../../tests/tests/pos/surface/date.rs}}
```

However, there should be no _cyclic dependencies_ in the function definitions.

```rust
{{#include ../../../tests/tests/neg/error_messages/dfn_cycle.rs}}
```

## Uninterpreted Function Declarations

You can also declare _uninterpreted_ functions -- about which `flux` knows nothing
other than the congruence property -- and then use them in refinements. Note that
in this case you have to use a `trusted` annotation for the function (e.g. `is_valid`)
that asserts facts over the uninterpreted function

```rust
{{#include ../../../tests/tests/pos/surface/uif00.rs}}
```

```rust
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

```rust
{{#include ../../../tests/tests/pos/surface/hide00.rs}}
```

## Spec Functions in SMTLIB

By default `flux` inlines all such function definitions.

Monomorphic functions may _optionally_ be encoded
as functions in SMT by using the `FLUX_SMT_DEFINE_FUN=1`
environment variable.

## Type Holes

You can (sometimes!) use `_` in the `flux` signatures to omit the Rust components, e.g.

**Function Signatures**

```rust
{{#include ../../../tests/tests/pos/surface/type_holes00.rs}}
```

**Structs and Enums**

```rust
{{#include ../../../tests/tests/pos/surface/type_holes01.rs}}
```

**Type Aliases**

```rust
{{#include ../../../tests/tests/pos/surface/type_holes02.rs}}
```
