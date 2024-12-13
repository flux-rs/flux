#[repr(u32)]
#[derive(Copy, Clone, Debug)]
pub enum SyscallReturnVariant {
    Failure = 0,
    Success = 128,
}

#[flux_rs::sig(fn() -> u32[0])]
pub fn test() -> u32 {
    SyscallReturnVariant::Failure as u32
}
