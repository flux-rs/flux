# CI Failure Analysis Report

## Summary
The CI failure in the `toolchain-upgrade` branch is caused by a breaking change in rustc that added explicit lifetime parameters to `BoundRegionKind` and `BoundVariableKind` types.

## Rust Toolchain Upgrade Details
- **Previous version**: nightly-2026-01-17
- **New version**: nightly-2026-01-30 (rustc commit: 842bd5be253e17831e318fdbd9d01d716557cc75)
- **Commit range**: nightly-2026-01-17 to nightly-2026-01-30

## Breaking Change in rustc

### Responsible Commit
- **Commit SHA**: `25c13655072475476f6ff3f26dc5cfda39db44d8`
- **PR**: [rust-lang/rust#150271 - Move struct placeholder pt2](https://github.com/rust-lang/rust/pull/150271)
- **Author**: James Barford-Evans (Jamesbarford)
- **Merged**: January 29, 2026
- **Commit title**: "Part 2 refactoring of moving placeholder types to `rustc_type_ir`"

### What Changed
The commit moved type definitions from `rustc_middle` to `rustc_type_ir` and made them generic over the `Interner` trait:

1. **BoundRegionKind**: Changed from `pub enum BoundRegionKind` to `pub enum BoundRegionKind<I: Interner>`
   - Now requires an explicit lifetime parameter
   - Located in: `compiler/rustc_type_ir/src/binder.rs`

2. **BoundVariableKind**: Changed from `pub enum BoundVariableKind` to `pub enum BoundVariableKind<I: Interner>`
   - Now requires an explicit lifetime parameter
   - Located in: `compiler/rustc_type_ir/src/binder.rs`

3. **Additional change**: `BoundRegionKind::NamedAnon` was renamed to `BoundRegionKind::NamedForPrinting`

### Type Aliases in rustc_middle
In `compiler/rustc_middle/src/ty/sty.rs`:
```rust
pub type BoundRegionKind<'tcx> = ir::BoundRegionKind<TyCtxt<'tcx>>;
pub type BoundVariableKind<'tcx> = ir::BoundVariableKind<TyCtxt<'tcx>>;
```

## Compilation Errors in flux-rustc-bridge

The following errors occur when compiling with the new rustc version:

### Error 1: Implicit elided lifetime in lowering.rs
```
error[E0726]: implicit elided lifetime not allowed here
   --> crates/flux-rustc-bridge/src/lowering.rs:705:49
    |
705 | impl<'tcx> Lower<'tcx> for &'tcx rustc_ty::List<rustc_ty::BoundVariableKind> {
    |                                                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^ expected lifetime parameter
```
**Fix needed**: Add `<'_>` to `BoundVariableKind`

### Error 2: Missing lifetime in BoundVariableKind enum
```
error[E0106]: missing lifetime specifier
  --> crates/flux-rustc-bridge/src/ty/mod.rs:48:12
   |
48 |     Region(BoundRegionKind),
   |            ^^^^^^^^^^^^^^^ expected named lifetime parameter
```
**Fix needed**: Add lifetime parameter to enum definition and field

### Error 3: Missing lifetime in function return type
```
error[E0106]: missing lifetime specifier
  --> crates/flux-rustc-bridge/src/ty/mod.rs:57:57
   |
57 |     ) -> &'tcx rustc_middle::ty::List<rustc_middle::ty::BoundVariableKind> {
   |                                                         ^^^^^^^^^^^^^^^^^ expected named lifetime parameter
```
**Fix needed**: Add `<'tcx>` to `BoundVariableKind`

### Error 4: Missing lifetime in BoundRegion struct
```
error[E0106]: missing lifetime specifier
   --> crates/flux-rustc-bridge/src/ty/mod.rs:453:15
    |
453 |     pub kind: BoundRegionKind,
    |               ^^^^^^^^^^^^^^^ expected named lifetime parameter
```
**Fix needed**: Add lifetime parameter to struct and field

### Error 5: Missing lifetime in type alias
```
error[E0106]: missing lifetime specifier
   --> crates/flux-rustc-bridge/src/ty/mod.rs:457:32
    |
457 |     type T = rustc_middle::ty::BoundRegion;
    |                                ^^^^^^^^^^^ expected named lifetime parameter
```
**Fix needed**: Add `<'tcx>` to `BoundRegion`

### Error 6: Removed enum variant
```
error[E0599]: no variant or associated item named `NamedAnon` found for enum `BoundRegionKind<I>` in the current scope
    --> crates/flux-rustc-bridge/src/ty/mod.rs:1173:34
     |
1173 |                 BoundRegionKind::NamedAnon(sym) => format!("{sym}"),
     |                                  ^^^^^^^^^ variant or associated item not found in `BoundRegionKind<TyCtxt<'_>>`
```
**Fix needed**: Replace `NamedAnon` with `NamedForPrinting`

## Files to Fix
1. `crates/flux-rustc-bridge/src/lowering.rs` - line 705
2. `crates/flux-rustc-bridge/src/ty/mod.rs` - lines 47-48, 57, 451-453, 457, 1173

## Required Changes Summary
All uses of `BoundRegionKind` and `BoundVariableKind` in flux-rustc-bridge need to be updated to include explicit lifetime parameters (typically `<'tcx>` or `<'_>`), and `NamedAnon` should be replaced with `NamedForPrinting`.
