# User's Guide

A list of various `flux` features as illustrated by examples in the regression tests.

## Index Refinements

Of the form `i32[e]` (`i32` equal to `e`) values.

```rust
{{#include ../../../tests/tests/pos/surface/index00.rs}}
```

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

## Requires Clauses

```rust
{{#include ../../../tests/tests/pos/surface/test01_where.rs}}
```
