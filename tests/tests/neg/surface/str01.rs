// TODO(nilehmann) think how to refine string slices and

#[flux::trusted]
#[flux::sig(fn(&str[@s]) -> usize[str_len(s)])]
fn str_len(s: &str) -> usize {
    s.len()
}

// move this test to pos
#[flux::sig(fn() -> usize[3])]
pub fn str01() -> usize {
    let x = "hog";
    str_len(x);
    x.len() //~ ERROR refinement type
}
