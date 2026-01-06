/// Test to check automatically lifted strong signatures,
/// see issue https://github.com/flux-rs/flux/issues/671

#[flux::refined_by(head: int)]
pub struct AssignmentUnsafe {
    #[flux::field({usize[head] | head >= 0})]
    head: usize,
}

fn set(s: &mut AssignmentUnsafe) {
    s.head = 0; // causes assignment might be unsafe, but it shouldn't
}
