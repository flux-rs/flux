// The refinements on the pointee of a raw pointer must also be stripped when they are inside
// nested generic arguments.

pub struct Wrap<T> {
    value: T,
}

#[flux::sig(fn(p: *const Wrap<i32{v: v > 0}>) -> i32{v: v > 0})]
pub unsafe fn single(p: *const Wrap<i32>) -> i32 {
    p.read().value //~ ERROR refinement type
}

#[flux::sig(fn(p: *const Wrap<Wrap<i32{v: v > 0}>>) -> i32{v: v > 0})]
pub unsafe fn nested(p: *const Wrap<Wrap<i32>>) -> i32 {
    p.read().value.value //~ ERROR refinement type
}

#[flux::sig(fn(p: *const Wrap<Wrap<Wrap<i32{v: v > 0}>>>) -> i32{v: v > 0})]
pub unsafe fn nested3(p: *const Wrap<Wrap<Wrap<i32>>>) -> i32 {
    p.read().value.value.value //~ ERROR refinement type
}

#[flux::sig(fn(p: *const Wrap<Wrap<i32[5]>>) -> i32[5])]
pub unsafe fn nested_idx(p: *const Wrap<Wrap<i32>>) -> i32 {
    p.read().value.value //~ ERROR refinement type
}
