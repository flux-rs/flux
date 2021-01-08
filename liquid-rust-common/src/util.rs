#[macro_export]
macro_rules! bug {
    () => {{
        unreachable!();
    }};
    ($msg:expr) => {{
        unreachable!($msg);
    }};
    ($fmt:expr, $($arg:tt)+) => ({
        unreachable!($fmt, $($arg)+);
    });
}

pub fn foo() {}
