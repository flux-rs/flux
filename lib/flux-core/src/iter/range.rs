use flux_attrs::*;

// TODO(RJ): use default spec `true` for `can_step_forward` and `can_step_backward`

defs! {
    fn default_step_can_step_forward<T>(start: T, count: int) -> bool;
    fn default_step_step_forward<T>(start: T, count: int) -> T;
    fn default_step_size<T>(lo: T, hi: T) -> int;
}

#[extern_spec(core::iter)]
trait Step {
    #![reft(
        fn can_step_forward(start: Self, count: int) -> bool {
            default_step_can_step_forward(start, count)
        }
        fn step_forward(start: Self, count: int) -> Self {
            default_step_step_forward(start, count)
        }
        fn size(lo: Self, hi: Self) -> int {
            default_step_size(lo, hi)
        }
    )]
    //
}

#[extern_spec(core::iter)]
impl Step for usize {
    #![reft(
        fn can_step_forward(start: int, count: int) -> bool  { start + count < usize::MAX }
        fn step_forward(start: int, count: int) -> int { start + count }
        fn size(lo: int, hi: int) -> int { hi - lo }
    )]
    //
}

#[extern_spec(core::iter)]
impl Step for i32 {
    #![reft(
        fn can_step_forward(start: int, count: int) -> bool  { start + count < i32::MAX }
        fn step_forward(start: int, count: int) -> int { start + count }
        fn size(lo: int, hi: int) -> int { hi - lo }
    )]
    //
}
