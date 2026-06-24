// A refined return type is not used after a call *through a function pointer*, so an
// otherwise-provable index bound is rejected. The identical program with a DIRECT call to
// `small` verifies today, which isolates the gap to the fn-pointer coercion/call rather than
// to the refinement or the indexing. Related to the `#[flux::trusted]` workaround + TODO in
// `tests/pos/fn_ptrs/fnptr00.rs` ("should actually support the below, not just leave it as
// `trusted`"), and possibly to the same broad FnPtr-refinement area as #1185 (which is an ICE,
// not this rejection). This program is Rust-safe (`i == 2`), so it should verify.
#![allow(unused)]

#[flux::sig(fn() -> usize{v: v < 3})]
fn small() -> usize { 2 }

// Direct call verifies:  let i = small(); let a = [0i32; 3]; let _ = a[i];
fn via_fn_ptr() {
    let p: fn() -> usize = small;
    let i = p(); // refined return `{v < 3}` is not carried through the call
    let a = [0i32; 3];
    let _ = a[i]; // flux: "possible out-of-bounds"; actually i == 2, in bounds
}
