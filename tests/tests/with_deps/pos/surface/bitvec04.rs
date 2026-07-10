// This test that we correctly resolve cases where a num var is first unified with a bitvec
// of unknown size and then a bitvector of known size
flux_rs::defs! {
    fn foo(x: bitvec<32>) -> bitvec<32> {
        x & bv_not(0xff)
    }
}
