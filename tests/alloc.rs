#![feature(register_tool)]
#![register_tool(liquid)]

// This requires:
// - Support for function calls.
// - Support for ADTs.
// - Support for measures.
// - Support for assumptions.
// - Support for field projections.
// - Support for immutable references.
// - Support for dereference projections.

// A custom pointer type.
#[derive(Copy, Clone)]
struct Ptr(*const u32);
// The address of the pointer.
#[liquid::measure("fn addr(Ptr) -> usize")]
// The size of the allocation to which the pointer belongs.
#[liquid::measure("fn alloc_size(Ptr) -> usize")]
// All the type annotations for these methods are assumed to be correct by liquid rust (and by
// Christian).
impl Ptr {
    // Do a new memory allocation able to hold `len` values of type u32 and return a pointer to the
    // start of allocation.
    #[liquid::assume_ty("fn(len: usize) -> {p: Ptr | addr(p) == 0 && len == alloc_size(p)}")]
    fn alloc(len: usize) -> Ptr {
        let layout = std::alloc::Layout::from_size_align(4 * len, 4).unwrap();
        let ptr = unsafe { std::alloc::alloc_zeroed(layout) };
        if ptr.is_null() {
            panic!("Out of memory");
        }

        Ptr(ptr as *const u32)
    }
    // Offset a pointer by `offset` bytes.
    #[liquid::assume_ty("fn(p: Ptr) -> {q: Ptr | addr(q) == addr(p) + offset}")]
    fn offset(self, offset: usize) -> Ptr {
        Ptr((self.0 as usize + offset) as *const u32)
    }
    // Dereference the pointer. This is safe to do if the pointer is not dangling (pointing outside
    // its allocation) and aligned (its address must be a multiple of 4).
    #[liquid::assume_ty("fn(p: {p: Ptr | addr(p) < alloc_size(p) && addr(p) % 4 == 0}) -> u32")]
    unsafe fn deref(self) -> u32 {
        *self.0
    }
}

// An array of `u32` integers.
struct Array {
    // A pointer to the base address of the allocation with the array's data.
    ptr: Ptr,
    // The length of the array.
    len: usize,
}

impl Array {
    // Create a new array.
    //
    // Liquid rust should verify that this array is backed by an allocation able to hold `len`
    // elements and that `array.ptr` points to the start of this allocation.
    #[liquid::ty("fn(len: usize) -> {array: Array | addr(array.ptr) == 0 && array.len == alloc_size(array.ptr)}")]
    pub fn new(len: usize) -> Array {
        let ptr = Ptr::alloc(len);
        Array { ptr, len }
    }

    // Get a pointer to an element of the array. This is safe because we aren't dereferencing the
    // pointer, just returning it.
    //
    // Liquid rust should verify that this function can only be called if `index` doesn't exceed
    // the length of the array. And if this is the case, that the returned pointer is non-dangling
    // and aligned.
    #[liquid::ty("fn(self: &Array, index: {i: usize | i < self.len}) -> {p: Ptr | addr(p) < alloc_size(p) && addr(p) % 4 == 0}")]
    fn get_unchecked(&self, index: usize) -> Ptr {
        self.ptr.offset(4 * index)
    }

    // Get an element of the array.
    //
    // Liquid rust should verify that this function can only be called if `index` doesn't exceed
    // the length of the array.
    #[liquid::ty("fn(self: &Array, index: {i: usize | i < self.index}) -> u32")]
    pub fn get(&self, index: usize) -> u32 {
        let ptr = self.get_unchecked(index);
        // Liquid rust should verify that this call can be done safely because the pointer is
        // non-dangling and aligned.
        unsafe { ptr.deref() }
    }
}

#[liquid::ty("fn(}) -> ()")]
fn main() {
    let array = Array::new(10);
    array.get(9);
    // Uncommenting the next line should trigger a compilation error
    // array.get(10);
}
