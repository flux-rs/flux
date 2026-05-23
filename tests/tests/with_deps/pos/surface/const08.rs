#[repr(u32)]
pub enum SyscallReturnVariant {
    Failure = 0,
}

#[flux_rs::sig(fn() -> u32[0])]
pub fn test() -> u32 {
    SyscallReturnVariant::Failure as u32
}
