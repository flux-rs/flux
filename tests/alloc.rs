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
// The ID of the allocation to which the pointer belongs (Each allocation has an unique ID and only
// pointers belonging to that allocation should be able to read from it).
#[liquid::measure("fn alloc_id(Ptr) -> usize")]
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
    // Increase a pointer by `offset` bytes. The resulting pointer belongs to the same allocation.
    #[liquid::assume_ty("fn(p: Ptr, o: offset) -> {q: Ptr | addr(q) == addr(p) + o && alloc_size(p) == alloc_size(q) && alloc_id(p) == alloc_id(q)}")]
    fn add(self, offset: usize) -> Ptr {
        Ptr((self.0 as usize + offset) as *const u32)
    }
    // Decrease a pointer by `offset` bytes. The resulting pointer belongs to the same allocation.
    #[liquid::assume_ty("fn(p: Ptr, o: offset) -> {q: Ptr | addr(q) == addr(p) - o && alloc_size(p) == alloc_size(q) && alloc_id(p) == alloc_id(q)}")]
    fn sub(self, offset: usize) -> Ptr {
        Ptr((self.0 as usize - offset) as *const u32)
    }
    // Dereference the pointer. This is safe to do if the pointer is not dangling (pointing outside
    // its allocation) and aligned (its address must be a multiple of 4).
    #[liquid::assume_ty("fn(p: {p: Ptr | addr(p) < alloc_size(p) && addr(p) % 4 == 0}) -> u32")]
    unsafe fn deref(self) -> u32 {
        *self.0
    }
    // Get the address of the pointer as an integer.
    #[liquid::assume_ty("fn(p: Ptr) -> usize")]
    fn addr(self) -> usize {
        self.0 as usize
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
    // the length of the array. And if this is the case, that the returned pointer is non-dangling,
    // aligned and that it belongs to the allocation backing the array.
    #[liquid::ty("fn(self: &Array, index: {i: usize | i < self.len}) -> {p: Ptr | addr(p) < alloc_size(p) && addr(p) % 4 == 0 && alloc_id(p) == alloc_id(self.ptr)}")]
    fn get_unchecked(&self, index: usize) -> Ptr {
        self.ptr.add(4 * index)
    }

    // Get an element of the array.
    //
    // Liquid rust should verify that this function can only be called if `index` doesn't exceed
    // the length of the array.
    #[liquid::ty("fn(self: &Array, index: {i: usize | i < self.index}) -> u32")]
    pub fn get(&self, index: usize) -> u32 {
        let ptr = self.get_unchecked(index);
        // Liquid rust should verify that this call can be done safely because the pointer is
        // non-dangling, aligned and it belongs to the allocation used to back the array.
        unsafe { ptr.deref() }
    }
}

#[liquid::ty("fn(}) -> ()")]
fn legal_access() {
    let array = Array::new(10);
    array.get(9);
}

#[liquid::ty("fn(}) -> ()")]
fn out_of_bounds_access() {
    let array = Array::new(10);
    // Classic out of bounds access. The array only has 9 elements. Liquid rust should error here
    // because the pointer used inside `get` has an address larger or equal to the allocation size.
    array.get(10);
}

#[liquid::ty("fn(}) -> ()")]
fn dangling_pointer_read() {
    // Create two arrays.
    let array1 = Array::new(10);
    let array2 = Array::new(10);
    // Create one valid pointer to each array.
    let ptr1 = array1.get_unchecked(0);
    let ptr2 = array2.get_unchecked(0);
    // Under the assumption that pointers are just numbers, this pointer should be equal to `ptr2`
    // because it is just `ptr1 - ptr1 + ptr2`. However it's still a pointer to `array1` and not
    // `array2`.
    let ptr3 = ptr1.sub(ptr1.addr()).add(pt2.addr());
    // Liquid rust should return an error here because `ptr3` has an address that cannot be proved
    // to be valid for `array1`.
    unsafe { ptr3.deref() };
}
