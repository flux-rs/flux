#![cfg_attr(flux, flux::defs {
    // A layout *fits* a block when the block is aligned to `layout.align()` and its size
    // lands between the size it was allocated with and the size actually handed back.
    // `NonNull` carries one size index, so we collapse that interval and track a block as
    // exactly the `layout.size()` it was allocated with; keeping only the upper bound would
    // admit deallocating with a smaller layout than was allocated, which is UB.
    // See: https://doc.rust-lang.org/std/alloc/trait.Allocator.html#memory-fitting
    //
    // Weaker than the "currently allocated via this allocator" the methods below require:
    // provenance, liveness and allocator identity are not checked, and the alignment checked
    // is the address's, not the one the block was allocated with. Those clauses are assumed.
    fn layout_fits(p: NonNull, l: Layout) -> bool {
        p.base == p.addr && l.size == p.size && p.addr % l.align == 0
    }
})]

// Unused to rustc — `Layout` appears only in `spec` attributes — but Flux resolves the
// `Layout` sort in `layout_fits` through this import.
#[allow(unused_imports)]
use core::{alloc::Layout, ptr::NonNull};

use flux_attrs::*;

#[extern_spec(core::alloc)]
trait Allocator {
    /// Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/mod.rs#L133
    /// On success the block meets the size and alignment guarantees of `layout`. The real
    /// block may be larger than `layout.size()`; we track it as exactly `layout.size()`,
    /// which under-approximates its extent — see `layout_fits`. Initialization is not
    /// tracked either, so reading out of a freshly allocated block type-checks.
    #[spec(fn(&Self, layout: Layout[@l])
        -> Result<NonNull<[u8]>{p: layout_fits(p, l)}, AllocError>)]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;

    /// Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/mod.rs#L150
    /// Same contract as `allocate`; that the block is zeroed is not modelled.
    #[spec(fn(&Self, layout: Layout[@l])
        -> Result<NonNull<[u8]>{p: layout_fits(p, l)}, AllocError>)]
    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;

    /// Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/mod.rs#L166
    /// - `ptr` must denote a block of memory currently allocated via this allocator
    ///   (assumed, not checked), and
    /// - `layout` must fit that block of memory.
    ///
    /// Deallocating does not invalidate `ptr`, so a later use of it is not rejected.
    #[spec(fn(&Self, ptr: NonNull<u8>[@p], layout: Layout[@l]) requires layout_fits(p, l))]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);

    /// Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/mod.rs#L206
    /// - `ptr` must denote a block of memory currently allocated via this allocator (assumed,
    ///   not checked),
    /// - `old_layout` must fit that block (`new_layout` need not), and
    /// - `new_layout.size()` must be greater than or equal to `old_layout.size()`.
    ///
    /// Note that `new_layout.align()` need not be the same as `old_layout.align()`.
    #[spec(fn(&Self, ptr: NonNull<u8>[@p], old_layout: Layout[@old], new_layout: Layout[@new])
        -> Result<NonNull<[u8]>{q: layout_fits(q, new)}, AllocError>
        requires layout_fits(p, old) && new.size >= old.size)]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>;

    /// Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/mod.rs#L269
    /// Same contract as `grow`; that the extra capacity is zeroed is not modelled.
    #[spec(fn(&Self, ptr: NonNull<u8>[@p], old_layout: Layout[@old], new_layout: Layout[@new])
        -> Result<NonNull<[u8]>{q: layout_fits(q, new)}, AllocError>
        requires layout_fits(p, old) && new.size >= old.size)]
    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>;

    /// Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/mod.rs#L333
    /// - `ptr` must denote a block of memory currently allocated via this allocator (assumed,
    ///   not checked),
    /// - `old_layout` must fit that block (`new_layout` need not), and
    /// - `new_layout.size()` must be smaller than or equal to `old_layout.size()`.
    ///
    /// Note that `new_layout.align()` need not be the same as `old_layout.align()`.
    #[spec(fn(&Self, ptr: NonNull<u8>[@p], old_layout: Layout[@old], new_layout: Layout[@new])
        -> Result<NonNull<[u8]>{q: layout_fits(q, new)}, AllocError>
        requires layout_fits(p, old) && new.size <= old.size)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>;
}
