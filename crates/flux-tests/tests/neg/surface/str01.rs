// TODO(nilehmann) think how to refine string slices and
// move this test to pos
#[flux::sig(fn() -> usize[3])]
pub fn str01() -> usize {
    let x = "str";
    x.len() //~ ERROR refinement type
}
