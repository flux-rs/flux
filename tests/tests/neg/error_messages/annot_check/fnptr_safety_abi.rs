// The safety and abi of a refined fn pointer must match the rust type

#[flux::spec(fn(f: fn(i32) -> i32{v: v > 0}) -> i32)] //~ ERROR incompatible refinement
pub fn call_unsafe(f: unsafe fn(i32) -> i32) -> i32 {
    unsafe { f(0) }
}

#[flux::spec(fn(f: fn(i32) -> i32{v: v > 0}) -> i32)] //~ ERROR incompatible refinement
pub fn call_extern(f: extern "C" fn(i32) -> i32) -> i32 {
    f(0)
}

// The same shape is fine for a safe, rust-abi fn pointer
#[flux::spec(fn(f: fn(i32) -> i32{v: v > 0}) -> i32{v: v > 0})]
pub fn call_safe(f: fn(i32) -> i32) -> i32 {
    f(0)
}
