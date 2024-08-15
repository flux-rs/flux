use std::{
    cell::Cell,
    fmt,
    panic::{Location, UnwindSafe},
};

use flux_config as config;
use rustc_errors::{ExplicitBug, MultiSpan};
use rustc_middle::ty::tls;
use rustc_span::{ErrorGuaranteed, Span};

thread_local! {
    static TRACKED_SPAN: Cell<Option<Span>> = const { Cell::new(None) };
}

pub fn track_span<R>(span: Span, f: impl FnOnce() -> R) -> R {
    TRACKED_SPAN.with(|cell| {
        let old = cell.replace(Some(span));
        let r = f();
        cell.set(old);
        r
    })
}

#[macro_export]
macro_rules! tracked_span_bug {
    () => ( $crate::tracked_span_bug!("impossible case reached") );
    ($msg:expr) => ({ $crate::bug::tracked_span_bug_fmt(::std::format_args!($msg)) });
    ($msg:expr,) => ({ $crate::tracked_span_bug!($msg) });
    ($fmt:expr, $($arg:tt)+) => ({
        $crate::bug::tracked_span_bug_fmt(::std::format_args!($fmt, $($arg)+))
    });
}

#[macro_export]
macro_rules! bug {
    () => ( $crate::bug!("impossible case reached") );
    ($msg:expr) => ({ $crate::bug::bug_fmt(::std::format_args!($msg)) });
    ($msg:expr,) => ({ $crate::bug!($msg) });
    ($fmt:expr, $($arg:tt)+) => ({
        $crate::bug::bug_fmt(::std::format_args!($fmt, $($arg)+))
    });
}

#[macro_export]
macro_rules! span_bug {
    ($span:expr, $msg:expr) => ({ $crate::bug::span_bug_fmt($span, ::std::format_args!($msg)) });
    ($span:expr, $msg:expr,) => ({ $crate::span_bug!($span, $msg) });
    ($span:expr, $fmt:expr, $($arg:tt)+) => ({
        $crate::bug::span_bug_fmt($span, ::std::format_args!($fmt, $($arg)+))
    });
}

#[track_caller]
pub fn bug_fmt(args: fmt::Arguments<'_>) -> ! {
    opt_span_bug_fmt(None::<Span>, args, Location::caller());
}

#[track_caller]
pub fn span_bug_fmt<S: Into<MultiSpan>>(span: S, args: fmt::Arguments<'_>) -> ! {
    opt_span_bug_fmt(Some(span), args, Location::caller());
}

#[track_caller]
pub fn tracked_span_bug_fmt(args: fmt::Arguments<'_>) -> ! {
    let location = Location::caller();
    TRACKED_SPAN.with(|span| opt_span_bug_fmt(span.get(), args, location))
}

#[track_caller]
fn opt_span_bug_fmt<S: Into<MultiSpan>>(
    span: Option<S>,
    args: fmt::Arguments<'_>,
    location: &'static Location<'static>,
) -> ! {
    tls::with_opt(move |tcx| {
        let msg = format!("{location}: {args}");
        match (tcx, span) {
            (Some(tcx), Some(span)) => tcx.dcx().span_bug(span, msg),
            (Some(tcx), None) => tcx.dcx().bug(msg),
            (None, _) => std::panic::panic_any(msg),
        }
    })
}

pub fn catch_bugs<R>(msg: &str, f: impl FnOnce() -> R + UnwindSafe) -> Result<R, ErrorGuaranteed> {
    if config::catch_bugs() {
        match std::panic::catch_unwind(f) {
            Ok(v) => Ok(v),
            Err(payload) => {
                tls::with_opt(move |tcx| {
                    let Some(tcx) = tcx else { std::panic::resume_unwind(payload) };

                    if payload.is::<ExplicitBug>() {
                        eprintln!("note: bug caught [{msg}]\n");
                        Err(tcx.dcx().delayed_bug("bug wasn't reported"))
                    } else {
                        eprintln!("note: uncaught panic [{msg}]\n");
                        std::panic::resume_unwind(payload)
                    }
                })
            }
        }
    } else {
        Ok(f())
    }
}
