#![feature(register_tool)]
#![register_tool(liquid)]

// Maybe this is impossible to satisfy without other assumptions. At least in 64-bit platforms this
// can be satisfied because pointers cannot have addresses larger than 2.pow(63).

// There might be a more interesting example involving the allocator API.

// FIXME: add support for assumptions.
// FIXME: add support for casts.
// FIXME: add support for raw immutable references.
#[liquid::assume("fn(p: *mut u32, c: {x: isize | (c as usize) + (p as usize) < 18446744073709551615usize}) -> *mut u32")]
unsafe fn offset(ptr: *mut u32, count: isize) -> *mut u32 {
    ptr.offset(count)
}
