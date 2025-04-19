# User's Guide

One day, this will be an actual user's guide.

For now, it is a collection of various `flux` features as illustrated by examples from the regression tests.

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

## Mixing Mutable and Strong References

```rust
{{#include ../../../tests/tests/pos/surface/local_ptr00.rs}}
```

## Refined Arrays

`flux` supports _refined arrays_ of the form `[i32{v: 0 <= v}; 20]`
denoting arrays of size `20` of non-negative `i32` values.

```rust
{{#include ../../../tests/tests/pos/array/array00.rs}}
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

## Refined Slices

```rust
{{#include ../../../tests/tests/pos/surface/slice00.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/rslice00.rs}}
```

## Refined `Vec`

This uses `extern_spec` which is described in the [specifications guide](specs.md).

**Standalone**

```rust
{{#include ../../../tests/tests/pos/vec/vec00.rs}}
```

**Associated Refinements** for indexing

```rust
{{#include ../../../tests/tests/lib/vec.rs}}
```

```rust
{{#include ../../../tests/tests/neg/surface/vec02.rs}}
```

## Named Function Signatures

You can also write _named_ function signatures using the `spec`
annotation (instead of the anonymous `sig` annotation).

## Requires Clauses

Used to specify preconditions in a single spot, if needed.

```rust
{{#include ../../../tests/tests/pos/surface/test01_where.rs}}
```

## Refining Structs

```rust
{{#include ../../../tests/tests/pos/structs/dot01.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/date.rs}}
```

### Invariants on Structs

```rust
{{#include ../../../tests/tests/pos/structs/invariant00.rs}}
```

with `const` generics

```rust
{{#include ../../../tests/tests/pos/surface/invariant_with_const_generic.rs}}
```

### Opaque Structs

See the [specifications guide](specs.md) for more about the `opaque` annotation.

```rust
{{#include ../../../tests/tests/pos/structs/opaque-range.rs}}
```

## Refining Enums

```rust
{{#include ../../../tests/tests/pos/enums/opt01.rs}}
```

```rust
{{#include ../../../tests/tests/pos/enums/pos00.rs}}
```

```rust
{{#include ../../../tests/tests/pos/enums/list00.rs}}
```

### Invariants on Enums

```rust
{{#include ../../../tests/tests/pos/enums/invariant00.rs}}
```

### Reflecting Enums

```rust
{{#include ../../../tests/tests/neg/surface/reflect00.rs}}
```

## Field Syntax for Indices

### Structs

```rust
{{#include ../../../tests/tests/pos/constructors/test00.rs}}
```

### Enums

```rust
{{#include ../../../tests/tests/pos/constructors/test01.rs}}
```

### Updates

```rust
{{#include ../../../tests/tests/pos/constructors/test03.rs}}
```

```rust
{{#include ../../../tests/tests/pos/constructors/test04.rs}}
```

```rust
{{#include ../../../tests/tests/pos/constructors/test05.rs}}
```

```rust
{{#include ../../../tests/tests/pos/constructors/test11.rs}}
```

## Const

You can use `int`-ish `const` in refinements e.g.

```rust
{{#include ../../../tests/tests/pos/surface/const07.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/const08.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/const10.rs}}
```

## Requires with `forall`

We allow a `forall` on the requires clauses, e.g.

```rust
{{#include ../../../tests/tests/pos/surface/forall01.rs}}
```

## Refined Associated Types

```rust
{{#include ../../../tests/tests/pos/refined_assoc_type/refined_assoc_type00.rs}}
```

## Pragma: `ignore`

Used to tell `flux` to _ignore_ (checking) a bunch of definitions.

```rust
{{#include ../../../tests/tests/neg/surface/ignore02.rs}}
```

## Pragma: `should_fail`

Used to tell `flux` to _expect_ a failure when checking a function.

```rust
{{#include ../../../tests/tests/pos/surface/should_fail.rs}}
```

## Const Generics

`flux` lets you use Rust's const-generics inside refinements.

**Refining Array Lengths**

```rust
{{#include ../../../tests/tests/neg/surface/const04.rs}}
```

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

### Plain Expressions

```rust
{{#include ../../../tests/tests/pos/surface/date.rs}}
```

### `let` binders

```rust
{{#include ../../../tests/tests/pos/surface/let-exprs00.rs}}
```

### Bounded Quantification

```rust
{{#include ../../../tests/tests/pos/surface/bounded_quant00.rs}}
```

### No Cycles!

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

### Function Signatures

```rust
{{#include ../../../tests/tests/pos/surface/type_holes00.rs}}
```

### Structs and Enums

```rust
{{#include ../../../tests/tests/pos/surface/type_holes01.rs}}
```

### Type Aliases

```rust
{{#include ../../../tests/tests/pos/surface/type_holes02.rs}}
```

### Generic Args

```rust
{{#include ../../../tests/tests/pos/surface/const11.rs}}
```

## Closures

```rust
{{#include ../../../tests/tests/pos/surface/closure00.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/closure02.rs}}
```

## Function Pointers

```rust
{{#include ../../../tests/tests/pos/surface/fndef00.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/fndef01.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/fndef02.rs}}
```

## Traits and Implementations

```rust
{{#include ../../../tests/tests/pos/surface/impl00.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/impl01.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/impl02.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/refined_fn_in_trait_01.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/trait-subtyping01.rs}}
```

## Impl Trait

```rust
{{#include ../../../tests/tests/pos/impl_trait/impl_trait00.rs}}
```

```rust
{{#include ../../../tests/tests/pos/impl_trait/impl_trait01.rs}}
```

## Dynamic Trait Objects

```rust
{{#include ../../../tests/tests/neg/trait_objects/dyn01.rs}}
```

## Generic Refinements

`flux` supports _generic refinements_ see [this paper for details](https://dl.acm.org/doi/10.1145/3704885)

**Horn Refinements**

```rust
{{#include ../../../tests/tests/pos/abstract_refinements/test00.rs}}
```

```rust
{{#include ../../../tests/tests/pos/abstract_refinements/test01.rs}}
```

```rust
{{#include ../../../tests/tests/pos/abstract_refinements/test03.rs}}
```

**Hindley Refinements**

TODO

## Bitvector Refinements

### Operators

```rust
{{#include ../../../tests/tests/pos/surface/bitvec03.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/bitvec_const02.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/bv_ord.rs}}
```

### Specification functions

```rust
{{#include ../../../tests/tests/pos/surface/bitvec05.rs}}
```

### Extensions

```rust
{{#include ../../../tests/tests/neg/surface/bitvec02.rs}}
```

### Bitvector Constants

```rust
{{#include ../../../tests/tests/neg/surface/bitvec_const00.rs}}
```

## `char` Literals

```rust
{{#include ../../../tests/tests/pos/surface/char02.rs}}
```

## `String` Literals

```rust
{{#include ../../../tests/tests/neg/surface/str02.rs}}
```

## Extern Specs

The `extern_spec` is used to provide `flux` signatures for functions defined in _external_ crates. See the [specifications guide](specs.md) for more details.

### Functions

```rust
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_macro.rs}}
```

### Options

```rust
{{#include ../../../tests/tests/lib/option.rs}}
```

```rust
{{#include ../../../tests/tests/pos/enums/option00.rs}}
```

### Vec

```rust
{{#include ../../../tests/tests/lib/option.rs}}
```

### Structs

```rust
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_struct03.rs}}
```

```rust
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_impl03.rs}}
```

### Impls

```rust
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_impl00.rs}}
```

```rust
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_impl01.rs}}
```

### Traits

```rust
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_trait00.rs}}
```

### `for` loops with range `i..j`

To see how `flux` handles `for i in 0..n` style loops:

```rust
{{#include ../../../tests/tests/pos/surface/for_range00.rs}}
```

## Associated Refinements

### Basic

```rust
{{#include ../../../tests/tests/pos/surface/assoc_reft01.rs}}
```

### Check Subtyping at Impl

```rust
{{#include ../../../tests/tests/pos/surface/trait-subtyping08.rs}}
```

### Default

```rust
{{#include ../../../tests/tests/neg/surface/assoc_reft03.rs}}
```

### Use in Extern Spec

```rust
{{#include ../../../tests/tests/pos/extern_specs/extern_spec_trait00.rs}}
```

```rust
{{#include ../../../tests/tests/lib/vec.rs}}
```

```rust
{{#include ../../../tests/tests/lib/iter.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/iter02.rs}}
```

### Associated Types

```rust
{{#include ../../../tests/tests/neg/surface/assoc_reft02.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/assoc_reft04.rs}}
```

### Refined Associated Types

```rust
{{#include ../../../tests/tests/pos/refined_assoc_type/refined_assoc_type01.rs}}
```

## Checking Overflows

You can switch on overflow checking

- _globally_ [with a flag](http://localhost:3000/guide/run.html?highlight=cache#flux-flags) or
- _locally_ with an attribute as shown below

```rust
{{#include ../../../tests/tests/pos/surface/check_overflow00.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/check_overflow01.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/check_overflow02.rs}}
```

```rust
{{#include ../../../tests/tests/pos/surface/check_overflow03.rs}}
```
