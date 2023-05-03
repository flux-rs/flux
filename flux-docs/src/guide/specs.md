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

## Extern specs

Sometimes you may want to refine a struct or function that outside your code. We
refer to such a specification as an "extern spec," which is short for "external
specification."

Flux right now has rudimentary support for extern specs: they are supported for
functions, impls, and structs. Impls are only supported for structs and if you
have multiple impls for a struct (such as `&[T]` and `[T]`), those may conflict.
Structs only support opaque refinements.

### Import the procedural macros

In order to use an extern spec you need to add a dependency on
[`flux_attrs_proc_macros`](https://github.com/flux-rs/flux/tree/main/flux-attrs-proc-macros).
Right now this needs to be done as a local dependency since it is not published.
Below is an example of how you can include it, although the version may be
different.

```toml
[dependencies]
flux-attrs-proc-macros = { path = "path-to-flux/flux/flux-attrs-proc-macros", version = "0.1.0" }
```

Then in your code you will need to include the `extern_spec` attribute macro.

```
use flux_attrs_proc_macros::extern_spec;
```

### Extern functions

An example of refining an extern function can be found
[here](https://github.com/flux-rs/flux/blob/d49a74dc59b2b9bb1dda01ee019d0ab9a66cdd89/flux-tests/tests/pos/surface/extern_spec_macro.rs).

To define an extern spec on a function, you need to do three things, which
happen to correspond to each of the below lines.

```
#[extern_spec(std::mem)]
#[flux::sig(fn(&mut i32[@a], &mut i32{v : a < v }) -> ())]
fn swap(a: &mut i32, b: &mut i32);
```

1. Add the `#[extern_spec]` attribute. This attribute optionally takes a path;
   in the above example, this is `std::mem`. You can use this path to qualify
   the function. So in the above example, the function we are targeting has the
   full path of `std::mem::swap`.
2. Add a `#[flux::sig(...)]` attribute. This is required for any extern spec on
   a function. This signature behaves as if the `#[flux::trusted]` attribute was
   added, because we can't actually check the implementation. We just verify
   some simple things, like that the function arguments have compatible types.
3. Write a function stub that matches the external function.

If you do the above, you can use `std::mem::swap` as if it were refined by the
above type.

You shouldn't need to know the details, but here's how the macro works. It
parses the `std::mem` into a module path and then transforms the function into

```
#[flux::extern_spec]
#[flux::sig(fn(&mut i32[@a], &mut i32{v : a < v }) -> ())]
#[allow(unused, dead_code)]
fn __flux_extern_spec_swap(a: &mut i32, b: &mut i32) {
    std::mem::swap(a, b)
}
```

It does this to get information about the function `std::mem::swap` and its
arguments (this turns out to be difficult to do without giving the compiler
something to inspect and type check).

### Extern structs and impls

An example of refining an extern struct and impl can be found
[here](https://github.com/flux-rs/flux/blob/d49a74dc59b2b9bb1dda01ee019d0ab9a66cdd89/flux-tests/tests/pos/surface/extern_spec_impl.rs).
A simpler example just involving structs can be found
[here](https://github.com/flux-rs/flux/blob/d49a74dc59b2b9bb1dda01ee019d0ab9a66cdd89/flux-tests/tests/pos/surface/extern_spec_struct.rs).

The syntax for an extern spec on a struct is very similar to that for a
function. Once again, each line in the example happens to correspond to a step.

```
#[extern_spec(std::string)]
#[flux::refined_by(len: int)]
struct String;
```

1. Add the `#[extern_spec]` attribute. This attribute optionally takes a path;
   in the above example, this is `std::string`. You can use this path to qualify
   the function. So in the above example, the struct we are targeting has the
   full path of `std::string::String`.
2. Add a `#[flux::refined_by(...)]` attribute. This is required for any extern
   spec on a struct. Right now these attributes behave as if they were opaque
   (`#[flux::opaque]`), although we may support non-opaque extern structs.
3. Write a stub for the extern struct.

If you do the above, you can use `std::string::String` as if it were refined by
an integer index.

The syntax for an extern impl is a little different than that for functions or
structs.

```
#[extern_spec(std::string)]
impl String {
    #[flux::sig(fn() -> String[0])]
    fn new() -> String;

    #[flux::sig(fn(&String[@n]) -> usize[n])]
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

You shouldn't need to know the details, but here's how the above two macros expand.

For structs:
```
#[flux::extern_spec]
#[allow(unused, dead_code)]
#[flux::refined_by(len: int)]
struct __FluxExternSpecString(std::string::String);
```

For impls (this was translated manually so there might be some bugs):
```
#[allow(unused, dead_code)]
struct __FluxExternImplStructString;

#[allow(unused, dead_code)]
impl __FluxExternImplStructString {
    #[flux::extern_spec]
    #[flux::sig(fn() -> String[0])]
    #[allow(unused, dead_code)]
    fn __flux_extern_spec_new() -> String {
       std::string::String::new::<>() 
    }
    #[flux::extern_spec]
    #[flux::sig(fn(&String[@n]) -> usize[n])]
    #[allow(unused, dead_code)]
    fn __flux_extern_spec_len(s: &String) -> usize {
       std::string::String::len::<>(s) 
    }
}
```

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
