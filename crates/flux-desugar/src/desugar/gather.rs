//! Gathering is the process of building an [`Env`] for a surface item.
//!
//! # Explicit vs Implicit Scopes
//!
//! A parameter can be declared in a *explicit* scope like `fn<refine n: int>(i32[n])` or in an
//! *implicit* scope with the `@n`, `#n` or `x: T` syntax. Ghatering is the process of traversing
//! the surface syntax to build an [`Env`] which makes all the scopes explicit.
//!
//! # The `x: T` syntax
//!
//! Dealing with the `x: T` syntax requires special care as it can be used to declare parameters
//! for types that don't have an associated sort, which we can only determine in later phases. For
//! example, consider the following:
//!
//! ```ignore
//! fn foo<T as type>(x: T) { }
//! ```
//!
//! If `T` is declared with kind `type`, the name `x` cannot bind a refinement parameter. We want to
//! allow user to write `x: T` but report an error if `x` is ever used. This is in contrast with
//! writing `T[@n]` where we report an error at the definition site. To partially deal with this,
//! during gathering we check if parameters declared with `x: T` are ever used. If they are not, we
//! avoid generating a parameter in the resulting env.
//!
//! [`Env`]: env::Env
