fn try_get_8_bytes(s: &[u8]) -> &[u8; 8] {
    let try8 = s.get(0..8).unwrap();
    try8.try_into().unwrap()
}
