// A captured refined value's refinement is not propagated through the closure boundary to the
// call site, so a provable index bound is rejected. The program is Rust-safe (`n < 3`), so it
// should verify. Companion to `fnptr_refined_call.rs`: both lose a refinement across an
// indirection (fn pointer / closure) that a direct use would preserve.
#![allow(unused)]

#[flux::sig(fn(n: usize{n < 3}))]
fn via_closure(n: usize) {
    let g = || n; // captures n : usize{n < 3}
    let i = g();  // refinement not propagated through the closure call
    let a = [0i32; 3];
    let _ = a[i]; // flux: "possible out-of-bounds"; actually n < 3, in bounds
}
