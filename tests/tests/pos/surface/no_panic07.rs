#[flux::no_panic]
pub fn decode_bytes_be(buf: &[u8], out: &mut [u8]) {
    // This test checks that no-panic inference is able to resolve the
    // call to `iter().rev().enumerate()` and determine that it does not panic.
    let l = out.len();
    for (i, b) in buf[..out.len()].iter().rev().enumerate() {
        let x = 3;
    }
}
