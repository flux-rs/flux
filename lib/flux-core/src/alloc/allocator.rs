#![flux::defs {
    // A layout *fits* a memory block when the block is aligned to `layout.align()` and
    // `layout.size()` lands in `min ..= max`, where `min` is the size of the layout most
    // recently used to allocate the block and `max` is the actual size handed back by
    // `allocate`, `grow` or `shrink`.
    // See: https://doc.rust-lang.org/std/alloc/trait.Allocator.html#memory-fitting
    //
    // We collapse that interval. Those three methods return a block whose tracked size is
    // exactly the requested `layout.size()`, so `min == max == p.size` and one equation
    // covers both bounds. Only tracking the upper bound (`l.size <= p.size`) would let a
    // caller deallocate — or grow/shrink — with a layout *smaller* than the one it
    // allocated with, which is UB. The price is that the surplus an allocator may return
    // above `layout.size()` is dropped on the floor: it cannot be proven in bounds.
    //
    // The `base == addr` conjunct says the pointer denotes the *start* of its allocation,
    // which is what "currently allocated via this allocator" amounts to in our model:
    // every such pointer came out of `allocate`, `grow` or `shrink`.
    //
    // Alignment stays approximate: fitting demands the block was allocated with *the same*
    // alignment as `layout.align()`, but the pointer does not carry the alignment it was
    // allocated with, so all we can check is that its address is a multiple of it.
    fn layout_fits(p: NonNull, l: Layout) -> bool {
        p.base == p.addr && l.size == p.size && p.addr % l.align == 0
    }
}]

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
    /// which under-approximates its extent — see `layout_fits`.
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
