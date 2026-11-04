#![flux::opts(allow_raw_deref = "ok")]

extern crate flux_core;

#[repr(C, packed)]
struct Packed {
    a: u8,
    b: i16,
    c: f32,
}

pub fn test_write_unaligned_packed_c() {
    let mut s = Packed { a: 0, b: 1, c: 2.0 };
    let x: *mut f32 = std::ptr::addr_of_mut!(s.c);
    unsafe { std::ptr::write_unaligned(x, 4.0) };
}

pub fn test_read_unaligned_packed_c() {
    let mut s = Packed { a: 0, b: 1, c: 2.0 };
    let x: *mut f32 = std::ptr::addr_of_mut!(s.c);
    unsafe { std::ptr::read_unaligned(x as *const f32) };
}

pub fn test_read_unaligned_packed_b() {
    let mut s = Packed { a: 0, b: 1, c: 2.0 };
    let x: *mut i16 = std::ptr::addr_of_mut!(s.b);
    unsafe { std::ptr::read_unaligned(x as *const i16) };
}

#[derive(Copy, Clone)]
struct Inner {
    x: i32,
}

#[repr(C, packed)]
struct Outer {
    a: u8,
    inner: Inner,
}

pub fn test_write_unaligned_nested() {
    let mut o = Outer { a: 0, inner: Inner { x: 1 } };
    let x: *mut i32 = std::ptr::addr_of_mut!(o.inner.x);
    unsafe { std::ptr::write_unaligned(x, 4) };
}

pub fn test_read_unaligned_nested() {
    let mut o = Outer { a: 0, inner: Inner { x: 1 } };
    let x: *mut i32 = std::ptr::addr_of_mut!(o.inner.x);
    unsafe { std::ptr::read_unaligned(x as *const i32) };
}

struct Normal {
    a: u8,
    b: i16,
    c: f32,
}

pub fn test_write_normal_c() {
    let mut s = Normal { a: 0, b: 1, c: 2.0 };
    let x: *mut f32 = std::ptr::addr_of_mut!(s.c);
    unsafe { x.write(4.0) };
}

pub fn test_read_normal_c() {
    let mut s = Normal { a: 0, b: 1, c: 2.0 };
    let x: *mut f32 = std::ptr::addr_of_mut!(s.c);
    unsafe { std::ptr::read(x as *const f32) };
}

#[repr(C, packed(2))]
struct Packed2I16 {
    a: u8,
    b: i16,
}

pub fn test_write_packed2_i16() {
    let mut s = Packed2I16 { a: 0, b: 1 };
    let x: *mut i16 = std::ptr::addr_of_mut!(s.b);
    unsafe { x.write(4) };
}

#[repr(C, packed(2))]
struct Packed2F32 {
    a: u8,
    b: f32,
}

pub fn test_write_unaligned_packed2_f32() {
    let mut s = Packed2F32 { a: 0, b: 1.0 };
    let x: *mut f32 = std::ptr::addr_of_mut!(s.b);
    unsafe { std::ptr::write_unaligned(x, 4.0) };
}

#[repr(C, packed)]
union PackedUnion {
    a: i32,
    b: u8,
}

pub fn test_write_unaligned_packed_union() {
    let mut u = PackedUnion { a: 1 };
    let x: *mut i32 = std::ptr::addr_of_mut!(u.a);
    unsafe { std::ptr::write_unaligned(x, 4) };
}

#[repr(packed)]
struct RustPacked {
    a: i8,
    b: u16,
    c: i32,
}

pub fn test_write_unaligned_rust_packed_c() {
    let mut s = RustPacked { a: 0, b: 1, c: 2 };
    let x: *mut i32 = std::ptr::addr_of_mut!(s.c);
    unsafe { std::ptr::write_unaligned(x, 4) };
}

pub fn test_read_unaligned_rust_packed_c() {
    let mut s = RustPacked { a: 0, b: 1, c: 2 };
    let x: *mut i32 = std::ptr::addr_of_mut!(s.c);
    unsafe { std::ptr::read_unaligned(x as *const i32) };
}

#[repr(packed)]
struct RustPackedNewtype(Inner);

pub fn test_write_unaligned_rust_packed_newtype() {
    let mut s = RustPackedNewtype(Inner { x: 1 });
    let x: *mut i32 = std::ptr::addr_of_mut!(s.0.x);
    unsafe { std::ptr::write_unaligned(x, 4) };
}

#[repr(packed)]
union RustPackedUnion {
    a: f64,
    b: u8,
}

pub fn test_write_unaligned_rust_packed_union() {
    let mut u = RustPackedUnion { a: 1.0 };
    let x: *mut f64 = std::ptr::addr_of_mut!(u.a);
    unsafe { std::ptr::write_unaligned(x, 4.0) };
}

enum PackedEnum {
    A(Packed),
    B,
}

pub fn test_write_unaligned_enum_packed() {
    let mut e = PackedEnum::A(Packed { a: 0, b: 1, c: 2.0 });
    match &mut e {
        PackedEnum::A(s) => {
            let x: *mut f32 = std::ptr::addr_of_mut!(s.c);
            unsafe { std::ptr::write_unaligned(x, 4.0) };
        }
        _ => {}
    }
}

pub fn test_read_unaligned_enum_packed() {
    let mut e = PackedEnum::A(Packed { a: 0, b: 1, c: 2.0 });
    match &mut e {
        PackedEnum::A(s) => {
            let x: *mut f32 = std::ptr::addr_of_mut!(s.c);
            unsafe { std::ptr::read_unaligned(x as *const f32) };
        }
        _ => {}
    }
}

#[repr(C, packed)]
union NestedPackedUnion {
    inner: Inner,
    b: u8,
}

pub fn test_write_unaligned_nested_packed_union() {
    let mut u = NestedPackedUnion { inner: Inner { x: 1 } };
    let x: *mut i32 = unsafe { std::ptr::addr_of_mut!(u.inner.x) };
    unsafe { std::ptr::write_unaligned(x, 4) };
}

pub fn test_read_unaligned_const_packed_c() {
    let s = Packed { a: 0, b: 1, c: 2.0 };
    let x: *const f32 = std::ptr::addr_of!(s.c);
    unsafe { std::ptr::read_unaligned(x) };
}

pub fn test_read_unaligned_const_nested() {
    let o = Outer { a: 0, inner: Inner { x: 1 } };
    let x: *const i32 = std::ptr::addr_of!(o.inner.x);
    unsafe { std::ptr::read_unaligned(x) };
}

pub fn test_read_unaligned_const_packed_union() {
    let u = PackedUnion { a: 1 };
    let x: *const i32 = std::ptr::addr_of!(u.a);
    unsafe { std::ptr::read_unaligned(x) };
}

#[repr(C, packed(1))]
struct A {
    a: u8,
    b: i32,
}

static mut A: A = A { a: 0, b: 1 };

pub fn test_write_unaligned_static_mut_packed1() {
    let p: *mut A = unsafe { std::ptr::addr_of_mut!(A) };
    let x: *mut i32 = unsafe { p.cast::<u8>().add(std::mem::offset_of!(A, b)) }.cast();
    unsafe { std::ptr::write_unaligned(x, 4) };
}

pub fn test_write_static_mut_packed1_whole() {
    let x: *mut A = unsafe { std::ptr::addr_of_mut!(A) };
    unsafe { std::ptr::write(x, A { a: 0, b: 1 }) };
}

#[repr(C)]
pub struct Pair {
    fst: i32,
    snd: i32,
}

#[flux::spec(fn (p: *mut[@pp] Pair) requires
    flux_core::ptr::valid(pp, 8) && flux_core::ptr::aligned_to(pp, 4))]
pub fn test_offset_of(p: *mut Pair) {
    let q: *mut i32 = unsafe { p.cast::<u8>().add(std::mem::offset_of!(Pair, snd)) }.cast();
    unsafe { q.write(1) };
}
