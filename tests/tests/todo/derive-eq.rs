#[derive(Clone, Copy, PartialEq, Eq)]
pub enum WasiProto {
    Unknown,
    Tcp,
    Udp,
}
