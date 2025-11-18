# Simple Access Control

Hopefully, by this point, you have a reasonable idea of the main tools
that Flux provides for refining types to capture correctness
requirements. In this, our first case study, lets see how to use those
tools to implement a very simple *role-based access control* (RBAC)
system, where Flux will check that only users with appropriate
permissions are allowed to access different resources. In doing so,
we’ll get some more practice with the tools we have already seen, and
learn about various other aspects of Flux, including how to

1.  Lift enum *variants* up into refinements,

2.  Specifying *equality* using associated refinements,

3.  Write *detached* specifications,

4.  Define and use *refinement-level functions*.

```rust, editable, hidden
extern crate flux_core;
use flux_rs::{assert, attrs::*};
```

## Reflection

A bird flying high above our access-control system, or more plausibly,
an LLM attempting to summarize its code, would observe that it consists
of three main entities: *users* who want to access resources, *roles*
that are assigned to each user, and the *permissions* that may be
granted to each role.

**Roles** Lets suppose that we want to track three kinds of users:
administrators, members and guests. We might represent these three roles
using a Rust `enum`:

```rust, editable
#[reflect]
#[derive(Debug, Clone)]
pub enum Roles {
    Admin,
    Member,
    Guest,
}
```

**Reflection** The key new bit in the definition of `Role` is the
`#[reflect]` attribute, which tells Flux that we intend to use variants
of this `enum` inside refinements. Why not just automatically `reflect`
all `enum`s? Currently, only a very restricted subset of `enum`s are
reflected: those whose variants take *no* parameters. Hence, Flux
requires us to explicitly mark such `enum`s with the `#[reflect]`
attribute. For example, we can now write a function that checks if a
given role is an `Admin` and returns `true` if so, and `false`
otherwise.

```rust, editable
#[spec(fn (&Role[@r]) -> bool[r == Role::Admin])]
pub fn is_admin(r: &Role) -> bool {
    match r {
        Role::Admin => true,
        _ => false,
    }
}
```

**EXERCISE:** Complete the specification and implementation of
`is_guest` below. You cannot use `==` (yet) because, well, just try to
use it and see what happens!

```rust, editable
fn is_guest(r: &Role) -> bool {
    true
}
```

When you are done, all the `assert` statements in the `test_role`
function should be verified by Flux.

```rust, editable
fn test_role() {
  let admin = Role::Admin;
  let member = Role::Member;
  let guest = Role::Guest;
  assert(is_admin(&admin) && !is_admin(&member) && !is_admin(&guest));
  assert(!is_guest(&admin) && !is_guest(&member) && is_guest(&guest));
}
```

## Defining Equality

My love and appreciation of pattern-matching should not be questioned.
However, sometimes we just want an old-fashioned equality test, for
instance, to make `is_admin` and `is_guest` trivial one-liners instead
of all the ceremony of a function-call wrapped inside a `match`
statement. Despite my telling you not to use `==` above, I’m pretty
certain that you tried it anyway. Or perhaps you anticipated that you
*could not* use it because we have not yet implemented the `PartialEq`
trait for `Role` which is what Rust uses to implement `==` and `!=`
comparisons.

**A Refined PartialEq Trait** The Flux standard library refines `std`‘s
`PartialEq` trait with two *associated refinements* (see
[this chapter](ch09_traits).md) `is_eq` and `is_ne` that respectively specify when two
values of the type implementing `PartialEq` are equal or not. The
*methods* `eq` and `ne` return boolean values `v` such that the
predicate `is_eq(r1, r2, v)` and `is_ne(r1, r2, v)` hold. By default,
the two associated refinements are just `true`, meaning that the `bool`
result `v` is unconstrained: it can be either `true` or `false`
regardless of the inputs.

``` rust
#[assoc(
    fn is_eq(x: Self, y: Rhs, v: bool) -> bool { true }
    fn is_ne(x: Self, y: Rhs, v: bool) -> bool { true }
)]
trait PartialEq<Rhs: PointeeSized = Self>: PointeeSized {
    #[spec(fn(&Self[@s], &Rhs[@t]) -> bool{v: Self::is_eq(s, t, v)})]
    fn eq(&self, other: &Rhs) -> bool;

    #[spec(fn(&Self[@s], &Rhs[@t]) -> bool{v: Self::is_ne(s, t, v)})]
    fn ne(&self, other: &Rhs) -> bool;
}
```

**A Refined PartialEq Implementation** However, for particular
implementations of `PartialEq`, *e.g.* for `Role`, we can define the
associated refinements to capture exactly when two values are equal or
not.

```rust, editable
#[assoc(
    fn is_eq(x: Self, y: Rhs, res: bool) -> bool { res <=> (r1 == r2) }
    fn is_ne(x: Self, y: Rhs, res: bool) -> bool { true }
)]
impl PartialEq for Role {
    #[spec(fn(&Self[@r1], &Self[@r2]) -> bool[r1 == r2]))]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Role::Admin, Role::Admin) => true,
            (Role::User, Role::User) => true,
            (Role::Guest, Role::Guest) => true,
            _ => false,
        }
    }
}
```

Now that we’ve *implemented* `PartialEq`, we can now write a simple
tests to check to see if Flux can understand when two `Role`s are equal
or not.

```rust, editable
fn test_role_eq() {
  let admin = Role::Admin;
  let member = Role::Member;
  assert(admin == admin);
  assert(admin != member);
  assert(member == member);
}
```

**EXERCISE:** Oh no! Why does Flux fail to verify that `admin != member`
in `test_role_eq`? Can you go back and figure out what bit of the above
to edit and fix, so that all the `assert` calls in `test_role_eq` are
verified by Flux.

**Permissions** Next, lets define the different kinds of permissions
that users may have to access resources. Again, we can use an `enum`
with a `#[reflect]` attribute.

```rust, editable
#[reflect]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Permissions { Read, Write, Comment, Delete, Configure }
```

Its rather tiresome to have to write out the full `PartialEq`
implementation, especially since we can automatically *derive* it using
Rust’s `#[derive(PartialEq)]`. However, now we are in a bit of a pickle.
When we explicitly wrote out the `eq` and `ne` methods above, we could
write an output type `bool[r1 == r2]` or `bool[r1 != r2]` respectively.
But now, we need a way to *retroactively* give Flux a specification for
the `eq` and `ne` methods. [^1]

## Detached Specifications

Normally, Flux specifications are *attached* to the function or type or
trait using a Rust attribute like `#[spec(...)]` or `#[reflect]`.
However, for situations like this, where you *cannot* modify the
original source because *e.g.* it is generated by a `derive` macro, or
perhaps because you’d rather just put the specifications elsewhere for
stylistic reasons, Flux also lets you write specifications that are
*detached* from their home in the source code. [^2]

```rust, editable
#[specs {
  impl std::cmp::PartialEq for Permissions {
    #[reft]
    fn is_eq(p1: Permissions, p2: Permissions, v:bool) -> bool {
       v <=> (p1 == p2)
    }
    #[reft]
    fn is_ne(p1: Permissions, p2: Permissions, v:bool) -> bool {
       v <=> (p1 != p2)
    }
    fn eq(&Self[@r1], &Self[@r2]) -> bool[r1 == r2];
  }
}]
const _: () = (); // just need something to attach the attribute to
```

The above “detached specification” says that we are providing
specifications for the `PartialEq` implementation for `Permissions`.
Flux will check these specifications against the (in this case, derived)
code, and will then let you use `==` and `!=` on `Permissions` values.

```rust, editable
fn test_eq_perms() {
    let read = Permissions::Read;
    let write = Permissions::Write;
    assert(read == read);
    assert(read != write);
}
```

## Refinement Level Functions

Now, that we’ve defined `Role`s and `Permission`s, we can define a
`User` struct that has their `id` and `role`, where we use a Flux index
to track the `role` of each `User`.

```rust, editable
#[refined_by(role: Role)]
pub struct User {
    pub name: String,
    #[field(Role[role])]
    pub role: Role,
}
```

**EXERCISE:** Complete the *specification* and *implementation* of the
`new` method so that the code in `test_user` verifies.

```rust, editable
impl User {
    // fill in the spec
    pub fn new(name: String, role: Role) -> Self {
        User { name, role  }
    }
}

fn test_user() {
    let alice = User::new("Alice".to_string(), Role::Admin);
    let bob = User::new("Bob".to_string(), Role::Guest);
    assert(alice.is_admin());
    assert(bob.is_guest());
}
```

**Policies** Lets *restrict* the set of `Permission`s that a `User` can
have based on their `Role`. For instance, suppose we want a policy where

- `Admin`s can do everything (i.e., have all `Permission`s),

- `Member`s can `Read`, `Write` and `Comment`, but not `Delete` or
  `Configure`,

- `Guest`s can only `Read`.

We can stipulate this policy in a *refinement-level function*
`permitted` that returns `true` exactly when a given `Role` is allowed
to have a given `Permission`.

```rust, editable
defs! {
    fn permitted(r: Role, p: Permissions) -> bool {
        if r == Role::Admin {
            true
        } else if r == Role::Member {
            p != Permissions::Delete && p != Permissions::Configure
        } else { // Guest
            p == Permissions::Read
        }
    }
}
```

**Enforcement** And now, we can use `permitted` to specify that only
users with the appropriate `Role` are allowed to perform certain
actions.

```rust, editable
impl User {
  #[spec(fn(&Self[@u]) requires permitted(u.role, Permissions::Read))]
  fn read(&self) { /* ... */ }
  #[spec(fn(&Self[@u]) requires permitted(u.role, Permissions::Write))]
  fn write(&self) { /* ... */ }
}
```

Flux will allow valid accesses,

```rust, editable
fn test_access_ok() {
    let alice = User::new("Alice".to_string(), Role::Admin);
    alice.configure();
    alice.delete();
}
```

but will swiftly reject, at compile-time, accesses that violate the
policy:

```rust, editable
fn test_access_bad() {
    let bob = User::new("Bob".to_string(), Role::Guest);
    bob.write();         // error!
    bob.delete();        // error!
    bob.configure();     // error!
}
```

## Summary

To recap, in this chapter we saw how to use

- *Reflect* `enum`s, *e.g.* to refer to variants like `Role::User` in
  refinements,

- *Detached* specifications for (derived) code *e.g.* `PartialEq`
  implementations,

- *Refinement-level functions* to specify contracts, *e.g.* policies on
  Roles,

which together, let us implement a simple role-based access control
system where Flux verifies that `User`s only access resources compatible
with their `Role`. Next, in [this chapter](ch12_sets,.md) we will see how to extend
our system with *set-valued* refinements that will allow for more
expressive access control.

[^1]: From [this chapter](ch08_externs.md) you may recall the notion of *extern
    specifications*; sadly we cannot quite use those because they are
    for things defined outside the current crate.

[^2]: Yes indeed, the code below is a *lot* of boilerplate, that is best
    generated by a macro, as we will see shortly, in [this chapter](ch12_sets.md).
