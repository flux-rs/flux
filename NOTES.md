# RJ Notes

- [+] `#[flux::ignore]`

- [+] `Constr(T, p)` to allow struct-invariants (Define `Rng[@lo, @hi]` with constraint `lo < hi`)

- [ ] Global constants e.g. `LINEAR_MEM_SIZE`

- [ ] [Recursive-Types and Measures](https://hackmd.io/q7KU5P4dTXG4t0F60aIiOg)
    - Special case to allow `@` under `Box`

- [ ] Projection? (Get `iter` working _without_ refinements... e.g. on plain `Vec`)

- [ ] Closure/FnPtr?

## Adding Constant Symbols to Rename/Env/Constraint

- `replace_bvars_with_fresh_vars`
- `Checker::init` returns the `env: TypeEnv` starting off


- PRODUCE a `ty::NameMap` which is `core::Name -> Entry`
- use this to CREATE `LoweringCtxt`


0. Use IndexGen to make a persistent/shared name_map
        const_names: Vec<(Symbol, Name)>,
        Map :: DefId ->
                ConstInfo {
                    def_id : LocalDefId,
                    sym    : Symbol,
                    name   : Name,
                    sort   : Sort,
                    constr : Constraint,
                    val    : Val
                }

1. Create `global_consts: Vec<Constraint>` ...
    - field in `genv` - in `register_const_sig`?

2. Use the `global_consts.size()` to build ParamCtxt
    - skip N elems where N is the size

3. To `genv` add a `global_consts: Constraints`
    - each `Constraint` is  `Path` and a `Ty`
    - each `Path` is a `FreeVar(Name)`

4. To `Checker::init` pass in `global_consts` as extra param
    - add the bindings in `init_constr`

## JUNK


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


From `collector.rs`

```rust
    // TRAIT-IMPL-OLD
    fn parse_trait_impl(&mut self, impl_item: &ImplItem, trait_impl_ids: &mut HashSet<DefId>) {
        let impl_def_id = impl_item.def_id;
        if let Some(real_impl_def_id) = self.tcx.impl_of_method(impl_def_id.to_def_id()) {
            if !trait_impl_ids.contains(&real_impl_def_id) {
                trait_impl_ids.insert(real_impl_def_id);
                if let Some(trait_ref) = self.tcx.impl_trait_ref(real_impl_def_id) {
                    if let Some(key) = rustc_substs_trait_ref_key(trait_ref.substs) {
                        let impl_ids = self.tcx.impl_item_implementor_ids(real_impl_def_id);
                        for (trait_f, ty_f) in impl_ids {
                            self.specs.trait_impls.insert((*trait_f, key), *ty_f);
                        }
                    }
                }
            }
        }
    }

    /// Returns the `DefId` of the trait being implemented by the `hir_id`
    fn _impl_item_trait_ref(tcx: TyCtxt<'tcx>, impl_item: &ImplItem) -> Option<DefId> {
        let hir_id = impl_item.hir_id();
        let parent = tcx.hir().get_parent_node(hir_id);

        let parent_node = tcx.hir().find(parent)?;

        match parent_node {
            rustc_hir::Node::Item(parent_item) => {
                match parent_item.kind {
                    ItemKind::Impl(parent_impl) => {
                        let trait_ref = parent_impl.of_trait.as_ref()?;
                        let self_ty = parent_impl.self_ty;
                        let trait_def_id = trait_ref.trait_def_id()?;
                        println!(
                            "TRACE: impl_item_trait_ref `{trait_def_id:?}` has `{self_ty:#?}`"
                        );
                        Some(trait_def_id)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
```
// TODO(RJ): TRAIT-OLD-STYLE
/// We want to build a lookup table: `(trait_f, key) -> trait_f_ty_at_key` that maps
/// (1) `trait_f` the generic method name `DefId` which appears at usage-sites,
/// (2) `key` the particular type-args at the usage site
/// to the `trait_f_ty_at_key` which is the specific method instance at the key
///
/// e.g. Given (std::Iterator.next, Rng) -> Rng.next
/// Table is creating a map: (method_def_id, subst) -> impl_def_id
///
pub type TraitRefKey = DefId;
pub type TraitImplMap = FxHashMap<(DefId, TraitRefKey), DefId>;

pub fn rustc_substs_trait_ref_key(
    substs: &rustc_middle::ty::List<rustc_middle::ty::subst::GenericArg>,
) -> Option<TraitRefKey> {
    match substs.get(0)?.unpack() {
        rustc_middle::ty::subst::GenericArgKind::Type(ty) => {
            match ty.kind() {
                rustc_middle::ty::TyKind::Adt(def, _) => Some(def.did()),
                _ => None,
            }
        }
        _ => None,
    }
}

// TODO:RJ gross to have to duplicate ...
pub fn flux_substs_trait_ref_key(substs: &List<GenericArg>) -> Option<TraitRefKey> {
    match substs.get(0)? {
        GenericArg::Ty(ty) => {
            match ty.kind() {
                TyKind::Adt(def_id, _) => Some(*def_id),
                _ => None,
            }
        }
    }
}

    // TODO: NUKE
    // fn _lookup_trait_impl_old(&self, trait_f: DefId, substs: &CallSubsts) -> Option<DefId> {
    //     let key = rustc::ty::flux_substs_trait_ref_key(&substs.lowered)?;
    //     let did_key = (trait_f, key);
    //     let trait_impl_id = self.trait_impls.get(&did_key)?;
    //     Some(*trait_impl_id)
    // }

Normalizing Experiments

in `lower_terminator`

```
                     // if let Ok(exp_ty) = self.tcx.try_expand_impl_trait_type(*fn_def, substs) {
                        //     let normal_exp_ty = self.tcx.subst_and_normalize_erasing_regions(
                        //         substs,
                        //         ParamEnv::empty(),
                        //         exp_ty,
                        //     );
                        //     // .normalize_erasing_regions(ParamEnv::empty(), exp_ty);
                        //     // .normalize_erasing_late_bound_regions(ParamEnv::empty(), exp_ty);

                        //     println!(
                        //         "TRACE: has_projections `{exp_ty:?}` = {:?}",
                        //         exp_ty.has_projections()
                        //     );
                        //     println!("TRACE: expand_impl_trait says: `{exp_ty:?}`");
                        //     println!("TRACE: normal_impl_trait says: `{normal_exp_ty:?}`");
                        // }
```


From `lower_ty`

```rust
        rustc_middle::ty::TyKind::Projection(proj_ty) => {
            // let ty = proj_ty.self_ty().kind();
            let trait_def_id = proj_ty.trait_def_id(tcx);
            let (trait_ref, own_substs) = proj_ty.trait_ref_and_own_substs(tcx);
            panic!("projection-type = `{proj_ty:?}` trait_def_id = `{trait_def_id:?}` trait_ref = `{trait_ref:?}` own_substs = `{own_substs:?}`")
        }
```

// TODO(RJ): LIFETIME-ARGS
// if path_args_len < rust_args.len() {
// for rust_arg in &rust_args[path_args_len..] {
// let ty = _default_generic_arg(rust_arg, path.span);
// args.push(ty)
// }
// }

// TODO(RJ): LIFETIME-ARGS
// fn _default_generic_arg(rust_arg: &rustc_ty::GenericArg, span: rustc_span::Span) -> Ty<Res> {
// match rust_arg {
// rustc_ty::GenericArg::Ty(ty) => default_ty(ty, span),
// }
// }
//
// fn default_ty(rust_ty: &rustc_ty::Ty, span: rustc_span::Span) -> Ty<Res> {
// match rust_ty.kind() {
// rustc_ty::TyKind::Adt(def_id, substs) => {
// let ident = Res::Adt(*def_id);
// let args = substs
// .iter()
// .map(|arg| default_generic_arg(arg, span))
// .collect();
// let path = Path { ident, args, span };
// Ty { kind: TyKind::Path(path), span }
// }
// _ => todo!(),
// }
// }

// TODO(RJ): LIFETIME-ARGS Keep this for next step where we "erase" lifetimes e.g. for real `Vec`
fn _lower_generic_arg_opt<'tcx>(
    tcx: TyCtxt<'tcx>,
    arg: rustc_middle::ty::subst::GenericArg<'tcx>,
) -> Option<Result<GenericArg, ErrorGuaranteed>> {
    match arg.unpack() {
        GenericArgKind::Type(ty) => {
            match lower_ty(tcx, ty) {
                Ok(lty) => Some(Ok(GenericArg::Ty(lty))),
                Err(e) => Some(Err(e)),
            }
        }
        _ => None,
    }
}
