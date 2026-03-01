// Minimal reproducer for the `assertion failed: !value.has_escaping_bound_vars()` ICE.
//
// Crashes on parent commit adc1d0f524 and on branch `trusted-pattern`.
// Does NOT crash on branch `escaping-var-hack` (commit b496e272b5) which fixes both:
//   (FIX a) fold.rs:   `Region::visit_with` and `GenericArg::Lifetime::visit_with` now
//                  call `visitor.visit_region` / visit the region, so `has_escaping_bvars()`
//                  correctly detects bound regions.
//   (FIX b) projections.rs: guard in `Normalizer::fold_sort` skips normalization when
//                        `alias_ty.has_escaping_bvars()` is true.
//       Without (a), (b) is dead code: `has_escaping_bvars()` always returns false.
//
// Crash path:
//   `foo`'s return type `P::Searcher<'_>` involves a GAT projection whose args
//   contain the late-bound lifetime of `s` (represented as `ReBound(0, ...)` inside
//   the fn-sig binder).
//
//   `refine_default(BaseTy::Alias(Projection, alias_ty))` in refining.rs calls
//   `bty.sort()` → `Sort::Alias(Projection, alias_ty_with_ReBound_0)`, then stores
//   it as `BoundVariableKind::Refine(sort, ...)` in an inner `Binder<SubsetTy>`.
//
//   `check_body` runs `replace_bound_vars` (shifts `ReBound(1)` in inner binder vars
//   back to `ReBound(0)`) then `deeply_normalize`.
//
//   `Binder::try_fold_with` folds the inner binder's VARS *before* entering the binder,
//   so `Normalizer::fold_sort` sees `Sort::Alias(Projection, alias_ty_with_ReBound_0)`
//   while the bound region is still "escaping".
//
//   `has_escaping_bvars()` should return true here (FIX a), triggering the guard (FIX b).
//   Without both fixes: `normalize_projection_ty_with_rustc` is called, rustc's
//   `erase_and_anonymize_regions` leaves `ReBound(...)` intact, and rustc's own
//   `deeply_normalize` panics with `assertion failed: !value.has_escaping_bound_vars()`.

trait MyPattern {
    type Searcher<'a>;
    fn into_searcher(self, haystack: &str) -> Self::Searcher<'_>;
}

fn foo<P: MyPattern>(s: &str, pat: P) -> P::Searcher<'_> {
    pat.into_searcher(s)
}
