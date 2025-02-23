use std::ops::ControlFlow;

use rustc_errors::{Diagnostic, ErrorGuaranteed};

pub trait ErrorEmitter {
    #[track_caller]
    fn emit<'a>(&'a self, err: impl Diagnostic<'a>) -> ErrorGuaranteed;
}

pub trait ErrorCollector<E> {
    type Result;

    fn collect(&mut self, err: E);

    fn into_result(self) -> Self::Result;
}

impl ErrorCollector<ErrorGuaranteed> for Option<ErrorGuaranteed> {
    type Result = Result<(), ErrorGuaranteed>;

    fn collect(&mut self, err: ErrorGuaranteed) {
        *self = Some(err).or(*self);
    }

    fn into_result(self) -> Self::Result {
        if let Some(err) = self { Err(err) } else { Ok(()) }
    }
}

pub trait ResultExt<T, E> {
    fn into_control_flow(self) -> ControlFlow<E, T>;

    fn collect_err(self, collector: &mut impl ErrorCollector<E>) -> Option<T>;

    #[track_caller]
    fn emit<'a>(self, emitter: &'a impl ErrorEmitter) -> Result<T, ErrorGuaranteed>
    where
        E: Diagnostic<'a>;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn into_control_flow(self) -> ControlFlow<E, T> {
        match self {
            Ok(v) => ControlFlow::Continue(v),
            Err(e) => ControlFlow::Break(e),
        }
    }

    fn collect_err(self, collector: &mut impl ErrorCollector<E>) -> Option<T> {
        match self {
            Ok(v) => Some(v),
            Err(err) => {
                collector.collect(err);
                None
            }
        }
    }

    #[track_caller]
    fn emit<'a>(self, emitter: &'a impl ErrorEmitter) -> Result<T, ErrorGuaranteed>
    where
        E: Diagnostic<'a>,
    {
        match self {
            Ok(v) => Ok(v),
            Err(err) => Err(emitter.emit(err)),
        }
    }
}
