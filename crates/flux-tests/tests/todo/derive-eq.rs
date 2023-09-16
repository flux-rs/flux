#![feature(register_tool)]
#![register_tool(flux)]

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum WasiProto {
    Unknown,
    Tcp,
    Udp,
}
