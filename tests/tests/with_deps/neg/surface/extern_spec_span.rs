extern crate flux_core;

fn test() {
    flux_rs::assert(false); //~ ERROR refinement type error

    let blah: Option<usize> = None;
    blah.unwrap(); //~ ERROR refinement type error
    // The "note" should mention `/flux-core/src/option.rs`  but looks like compiletest doesn't quite track that.
}
