# RJ Notes

- default_fn_sig
- refine_fn_sig

https://internals.rust-lang.org/t/accessing-the-defid-of-a-trait-implementation/17001


`with_self_ty` takes a `PolyFnSig` aka `Binder<T>` and replaces it by plugging in the `Self`

https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/sty/struct.Binder.html#method.with_self_ty-1

and produces a `PolyTraitRef` which you can then get a `DefId` from?

https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/sty/type.PolyTraitRef.html


What does this do?

https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.try_expand_impl_trait_type


impl_item_implementor_ids

aha. see notes for

https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.impl_item_implementor_ids

All implementations of a trait!

https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.find_map_relevant_impl


https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/context/struct.TyCtxt.html#method.implementations_of_trait


method-`DefId`
-----> impl-`DefId`  (using `impl_of_method`)
-----> trait-`DefId` (using `trait_id_of_impl`)


START with a method-`DefId`

**Step 1**

```rust
pub fn impl_of_method(self, def_id: DefId) -> Option<DefId>
```

If the given DefId describes a method belonging to an impl, returns the DefId of the impl that the method belongs to; otherwise, returns None.




```rust
pub fn trait_id_of_impl(self, def_id: DefId) -> Option<DefId>
```

Given the DefId of an impl, returns the DefId of the trait it implements. If it implements no trait, returns None.
source

Complete Reference to a Trait

https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/sty/struct.TraitRef.html

Pair of

- `DefId`    (the trait)
- `SubstRef` (the "args")
