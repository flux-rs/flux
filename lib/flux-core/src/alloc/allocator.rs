#![cfg_attr(flux, flux::defs {
    // A layout *fits* a memory block when the block is aligned to `layout.align()` and is
    // at least `layout.size()` bytes long. The `base == addr` conjunct additionally says
    // the pointer denotes the *start* of its allocation, which is what "currently
    // allocated via this allocator" amounts to in our model: every such pointer came out
    // of `allocate`, `grow` or `shrink`, and those all return the start of a block.
    //
    // The docs also bound `layout.size()` from below by the size originally requested from
    // `allocate`; we only track the actual size of the block, so that half is not modelled.
    // See: https://doc.rust-lang.org/std/alloc/trait.Allocator.html#memory-fitting
    fn layout_fits(p: NonNull, l: Layout) -> bool {
        p.base == p.addr && l.size <= p.size && p.addr % l.align == 0
    }
})]

use core::{alloc::Layout, ptr::NonNull};

use flux_attrs::*;

#[extern_spec(core::alloc)]
trait Allocator {
    /// Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/mod.rs#L133
    /// On success the block meets the size and alignment guarantees of `layout`; it may be
    /// larger than `layout.size()`, hence the `<=` inside `layout_fits`.
    #[spec(fn(&Self, layout: Layout[@l])
        -> Result<NonNull<[u8]>{p: layout_fits(p, l)}, AllocError>)]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;

    /// Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/mod.rs#L150
    /// Same contract as `allocate`; that the block is zeroed is not modelled.
    #[spec(fn(&Self, layout: Layout[@l])
        -> Result<NonNull<[u8]>{p: layout_fits(p, l)}, AllocError>)]
    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;

    /// Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/mod.rs#L166
    /// - `ptr` must denote a block of memory currently allocated via this allocator, and
    /// - `layout` must fit that block of memory.
    #[spec(fn(&Self, ptr: NonNull<u8>[@p], layout: Layout[@l]) requires layout_fits(p, l))]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);

    /// Core impl: https://github.com/rust-lang/rust/blob/dab8d9d1066c4c95008163c7babf275106ce3f32/library/core/src/alloc/mod.rs#L206
    /// - `ptr` must denote a block of memory currently allocated via this allocator,
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
    /// - `ptr` must denote a block of memory currently allocated via this allocator,
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
