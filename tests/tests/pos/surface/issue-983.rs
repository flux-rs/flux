pub struct FromFn<F>(F)
where
    F: Fn(&mut core::fmt::Formatter<'_>) -> core::fmt::Result;
