# Defining Indexes for Structs

[Online demo](http://goto.ucsd.edu:8091/index.html#?demo=structs.rs)

Previously, we've looked at how `flux` uses refinements to prevent things 
like [underflows][blog-intro] and to allow writing a refined vector API 
where all accesses are statically [bounds-checked][blog-vectors]. 
All these examples relied upon indexing *existing* types like 
`i32` or `bool` or `vec` (or wrappers around them) with logical 
representations.

This post shows how _you_ can define custom indices for types that you
create and use the indices to specify various application correctness 
conditions which can be verified by `flux` at compile-time.

## Box
- from github issue

## Date
- from tests?

## CSV
- from tests / LH blog

[blog-intro]: https://liquid-rust.github.io/2022/11/14/introducing-flux/
[blog-owners]: https://liquid-rust.github.io/2022/11/16/ownership-in-flux/
[bsearch]: https://doc.rust-lang.org/src/core/slice/mod.rs.html#2423-2425
