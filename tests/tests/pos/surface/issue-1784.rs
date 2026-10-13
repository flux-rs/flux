// The block joining the branches of the `if` is a dummy join that we skip, but it is also the
// immediate dominator of the loop head.

pub fn f(b: bool) {
    if b {}
    loop {}
}
