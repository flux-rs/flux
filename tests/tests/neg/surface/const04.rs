// https://github.com/flux-rs/flux/issues/625

const BUFLEN: usize = 100;

pub struct Blob {
    data: [i32; BUFLEN],
}

pub fn test(buf: &[i32; BUFLEN]) -> i32 {
    let x0 = buf[0];
    let x1 = buf[10];
    let x2 = buf[BUFLEN - 1];
    let xbad = buf[BUFLEN]; //~ ERROR assertion might fail
    x0 + x1 + x2 + xbad
}

pub fn test_blob(blob: Blob) -> i32 {
    let x0 = blob.data[0];
    let x1 = blob.data[10];
    let x2 = blob.data[BUFLEN - 1];
    let xbad = blob.data[BUFLEN]; //~ ERROR assertion might fail
    x0 + x1 + x2 + xbad
}
