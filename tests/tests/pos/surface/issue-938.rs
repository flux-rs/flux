flux_rs::defs! {
    fn bv_map_get(m: Map<int, bitvec<32>>, k:int) -> bitvec<32> { map_select(m, k) }
}
