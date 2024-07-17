pub fn read_u16(bytes: [u8; 2]) -> u16 {
    u16::from_le_bytes(bytes)
}

pub fn bob(n: u32) -> u8 {
    let arr = n.to_be_bytes();
    arr[0] + arr[1] + arr[2] + arr[3]
}
