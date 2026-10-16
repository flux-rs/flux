extern crate flux_core;

#[repr(C, packed)]
struct Packed {
    a: u8,
    b: i16,
    c: f32,
}

pub fn test_write_packed_c() {
    let mut s = Packed { a: 0, b: 1, c: 2.0 };
    let x: *mut f32 = std::ptr::addr_of_mut!(s.c);
    unsafe { x.write(4.0) }; //~ ERROR refinement type error
}

pub fn test_read_packed_c() {
    let mut s = Packed { a: 0, b: 1, c: 2.0 };
    let x: *mut f32 = std::ptr::addr_of_mut!(s.c);
    unsafe { std::ptr::read(x as *const f32) }; //~ ERROR refinement type error
}

pub fn test_read_packed_b() {
    let mut s = Packed { a: 0, b: 1, c: 2.0 };
    let x: *mut i16 = std::ptr::addr_of_mut!(s.b);
    unsafe { std::ptr::read(x as *const i16) }; //~ ERROR refinement type error
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

pub fn test_write_nested() {
    let mut o = Outer { a: 0, inner: Inner { x: 1 } };
    let x: *mut i32 = std::ptr::addr_of_mut!(o.inner.x);
    unsafe { x.write(4) }; //~ ERROR refinement type error
}

pub fn test_read_nested() {
    let mut o = Outer { a: 0, inner: Inner { x: 1 } };
    let x: *mut i32 = std::ptr::addr_of_mut!(o.inner.x);
    unsafe { std::ptr::read(x as *const i32) }; //~ ERROR refinement type error
}

#[repr(C, packed(2))]
struct Packed2F32 {
    a: u8,
    b: f32,
}

pub fn test_write_packed2_f32() {
    let mut s = Packed2F32 { a: 0, b: 1.0 };
    let x: *mut f32 = std::ptr::addr_of_mut!(s.b);
    unsafe { x.write(4.0) }; //~ ERROR refinement type error
}

#[repr(C, packed)]
union PackedUnion {
    a: i32,
    b: u8,
}

pub fn test_write_packed_union() {
    let mut u = PackedUnion { a: 1 };
    let x: *mut i32 = std::ptr::addr_of_mut!(u.a);
    unsafe { x.write(4) }; //~ ERROR refinement type error
}

#[repr(packed)]
struct RustPacked {
    a: i8,
    b: u16,
    c: i32,
}

pub fn test_write_rust_packed_c() {
    let mut s = RustPacked { a: 0, b: 1, c: 2 };
    let x: *mut i32 = std::ptr::addr_of_mut!(s.c);
    unsafe { x.write(4) }; //~ ERROR refinement type error
}

pub fn test_read_rust_packed_c() {
    let mut s = RustPacked { a: 0, b: 1, c: 2 };
    let x: *mut i32 = std::ptr::addr_of_mut!(s.c);
    unsafe { std::ptr::read(x as *const i32) }; //~ ERROR refinement type error
}

#[repr(packed)]
struct RustPackedNewtype(Inner);

pub fn test_write_rust_packed_newtype() {
    let mut s = RustPackedNewtype(Inner { x: 1 });
    let x: *mut i32 = std::ptr::addr_of_mut!(s.0.x);
    unsafe { x.write(4) }; //~ ERROR refinement type error
}

#[repr(packed)]
union RustPackedUnion {
    a: f64,
    b: u8,
}

pub fn test_write_rust_packed_union() {
    let mut u = RustPackedUnion { a: 1.0 };
    let x: *mut f64 = std::ptr::addr_of_mut!(u.a);
    unsafe { x.write(4.0) }; //~ ERROR refinement type error
}

enum PackedEnum {
    A(Packed),
    B,
}

pub fn test_write_enum_packed() {
    let mut e = PackedEnum::A(Packed { a: 0, b: 1, c: 2.0 });
    match &mut e {
        PackedEnum::A(s) => {
            let x: *mut f32 = std::ptr::addr_of_mut!(s.c);
            unsafe { x.write(4.0) }; //~ ERROR refinement type error
        }
        _ => {}
    }
}

pub fn test_read_enum_packed() {
    let mut e = PackedEnum::A(Packed { a: 0, b: 1, c: 2.0 });
    match &mut e {
        PackedEnum::A(s) => {
            let x: *mut f32 = std::ptr::addr_of_mut!(s.c);
            unsafe { std::ptr::read(x as *const f32) }; //~ ERROR refinement type error
        }
        _ => {}
    }
}

#[repr(C, packed)]
union NestedPackedUnion {
    inner: Inner,
    b: u8,
}

pub fn test_write_nested_packed_union() {
    let mut u = NestedPackedUnion { inner: Inner { x: 1 } };
    let x: *mut i32 = unsafe { std::ptr::addr_of_mut!(u.inner.x) };
    unsafe { x.write(4) }; //~ ERROR refinement type error
}

pub fn test_read_const_packed_c() {
    let s = Packed { a: 0, b: 1, c: 2.0 };
    let x: *const f32 = std::ptr::addr_of!(s.c);
    unsafe { x.read() }; //~ ERROR refinement type error
}

pub fn test_read_const_nested() {
    let o = Outer { a: 0, inner: Inner { x: 1 } };
    let x: *const i32 = std::ptr::addr_of!(o.inner.x);
    unsafe { std::ptr::read(x) }; //~ ERROR refinement type error
}

pub fn test_read_const_packed_union() {
    let u = PackedUnion { a: 1 };
    let x: *const i32 = std::ptr::addr_of!(u.a);
    unsafe { x.read() }; //~ ERROR refinement type error
}
