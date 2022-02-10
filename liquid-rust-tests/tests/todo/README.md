# Todo features
A list of currently unsupported features that would be useful along with examples.

## Major

### Struct types
Having liquid types for structs would be highly useful for writing and checking invariants of structs. In [this example](struct_types/simple_example.rs), a translation of [a similar example from liquid haskell](http://goto.ucsd.edu:8090/index.html#?demo=permalink%2F1642157817_3971.hs), a struct has the invariant that two of its fields have the same length. The example demonstrates two different ways of writing the invariant, one putting the invariant internally in the types of the fields, and the other using a ghost field to express the invariant.

#### Examples
* [simple_example](struct_types/simple_example.rs)

### Better loop invariant inference (user-specified qualifiers)
Right now, the loop invariants getting inferred sometimes aren't strong enough to proof things. For example, in [fib](loop_invariants/fib.rs), the loop invariant `i > 0 && j >= 0` doesn't seem to be getting inferred, which is necessary to prove the postcondition. In [gcd](loop_invariants/gcd.rs), the invariant `a > 0 && b > 0` isn't able to be inferred, although there may also be an issue with using modulo ([see below](#support-for-modulo)).

#### Examples
* [fib.rs](loop_invariants/fib.rs)
* [gcd.rs](loop_invariants/gcd.rs)

## Minor

### Support for modulo
Low priority, used in [gcd](loop_invariants/gcd.rs), for example.