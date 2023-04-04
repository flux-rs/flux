# Flux Specification Guide

This is a WIP guide to writing specifications in `flux`.

## Refinement Types

- **Indexed Type**: An indexed type `B[r]` is composed of a base Rust type `B` and a refinement index `r`. The meaning of the index depends on the type. Some examples are
  - `i32[n]`: denotes the (singleton) set of `i32` values equal to `n`.
  - `List<T>[n]`: values of type `List<T>` of length `n`.

- **Refinement parameter**: Function signatures can be parametric on refinement variables. Refinement parameters are declared using the `@n` syntax. For example, the following signature:

  `fn(i32[@n]) -> i32[n + 1]`

  binds `n` over the entire scope of the function to specify that it takes an `i32` equal to `n` and returns an `i32` equal to `n + 1`. This is analogous to languages like Haskell where a lower case letter can be used to quantify over a type, e.g., the type `a -> a` in Haskell is polymorphic on the type `a` which is bound for the scope of the entire function type.

- **Existential Type**: An existential type `B{v: r(v)}` is composed of a base type `B`, a refinement variable `v` and a refinement predicate `r` on `v`. Intuitively, a Rust value `x` has type `B{v: r(v)}` if there exists a refinement value `a` such that `r(a)` holds and `x` has type `B[x]`.
  - `i32{v: v > 0}`: set of positive `i32` values.
  - `List<T>{v: v > 0}`: set of non-empty lists.

- **Constraint Type**: A constraint type has the form `{T | r}` where `T` is any type (not just a base type). Intuitively, a value has type `{T | r}` if it has type `T` and also `r` holds. They can be used to constraint a refinement parameter. For example, the following signature constraint the refinement parameter `n` to be less than `n`.

  `fn({i32[@n] | n < 10}) -> i32[n + 1]`

  Constraint types serve a similar role as existentials as they can also be used to constraint some
  refinement value with a predicate, but an existential type can only be used to constraint refinement
  variable that it bound locally, in contrast constraint types can be used to constraint a "non-local" parameter. This can be seen in the example above where the parameter `n` cannot be bound locally
  because it has to be used in the return type.

## Argument Syntax

The `@n` syntax used to declare refinements parameters can be hard to read sometimes. Flux also supports a syntax that let you bind refinement parameters using colons similar to the syntax used to declare arguments in a function. We call this *argument syntax*. This syntax desugars to one of the refinements forms discussed above. For example, the following signature

`fn(x: i32, y: i32) -> i32[x + y]`

desugars to

`fn(i32[@x], i32[@y]) -> i32[x + y]`

It is also possible to attach some constraint to the parameters when using argument syntax. For example,
to specify that `y` must be greater than `x` using argument syntax we can write:

`fn(x: i32, y: i32{x > y}) -> i32[x + y]`

This will desugar to:

`fn(i32[@x], {i32[@y] | x > y}) -> i32[x + y]`

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
