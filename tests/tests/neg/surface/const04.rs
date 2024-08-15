// https://github.com/flux-rs/flux/issues/625

#[flux::constant]
const BUFLEN: usize = 100;

pub fn test(buf: &[i32; BUFLEN]) -> i32 {
    let x0 = buf[0];
    let x1 = buf[10];
    let x2 = buf[BUFLEN - 1];
    let xbad = buf[BUFLEN]; //~ ERROR assertion might fail
    x0 + x1 + x2 + xbad
}
