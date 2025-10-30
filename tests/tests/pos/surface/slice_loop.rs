// We want these two tests to pass _without_ scraping any qualifiers,
// because the contents of the slice do not actually _change_ across
// iterations of the loop.

extern crate flux_core;

#[flux_rs::spec(fn (&[i32{v:v > 666}]))]
pub fn test_while(vals: &[i32]) {
    let mut i = 0;
    while i < vals.len() {
        let val = vals[i];
        flux_rs::assert(val > 666);
        i += 1;
    }
}

#[flux_rs::spec(fn (&[i32{v:v > 666}]))]
pub fn test_for_index(vals: &[i32]) {
    let n = vals.len();
    for i in 0..n {
        let val = vals[i];
        flux_rs::assert(val > 666);
    }
}
