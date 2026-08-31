extern crate flux_core;

use std::ptr::NonNull;

// --- cast ---

#[flux::spec(fn(nn: NonNull<T>[@base, @addr, @size]) -> NonNull<U>[base, addr, size])]
pub fn test_cast_preserves_indices<T, U>(nn: NonNull<T>) -> NonNull<U> {
    nn.cast::<U>()
}

#[flux::spec(fn(nn: NonNull<i32>[@base, @addr, @size])
    requires addr >= base && addr > 0 && size >= 4 && addr % 4 == 0)]
pub fn test_cast_narrow_read(nn: NonNull<i32>) {
    let bytes = nn.cast::<u8>();
    unsafe {
        let _value = bytes.read();
    }
}

#[flux::spec(fn(nn: NonNull<i32>[@base, @addr, @size])
    requires addr >= base && addr > 0 && size >= 8 && addr % 8 == 0)]
pub fn test_cast_widen_read(nn: NonNull<i32>) {
    let wide = nn.cast::<i64>();
    unsafe {
        let _value = wide.read();
    }
}

#[flux::spec(fn(nn: NonNull<i32>[@base, @addr, @size])
    requires addr >= base && addr > 0 && size >= 4 && addr % 4 == 0)]
pub fn test_cast_byte_add_write(nn: NonNull<i32>) {
    let bytes = nn.cast::<u8>();
    unsafe {
        bytes.byte_add(3).write(255);
    }
}

#[flux::spec(fn(nn: NonNull<i32>[@base, @addr, @size])
    requires addr >= base && addr > 0 && size >= 4 && addr % 4 == 0)]
pub fn test_cast_round_trip(nn: NonNull<i32>) {
    let bytes = nn.cast::<u8>();
    let ints = bytes.cast::<i32>();
    unsafe {
        ints.write(10);
    }
}

pub fn test_cast_slice_bytes(buf: &mut [i32; 4]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    let bytes = nn.cast::<u8>();
    unsafe {
        let _last = bytes.byte_add(15).read();
    }
}
