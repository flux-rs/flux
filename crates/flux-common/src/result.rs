use rustc_errors::{Diagnostic, ErrorGuaranteed};

pub trait ErrorEmitter {
    #[track_caller]
    fn emit<'a>(&'a self, err: impl Diagnostic<'a>) -> ErrorGuaranteed;
}

pub trait ErrorCollector<E> {
    type Result;

    fn collect_err(&mut self, err: E);

    fn into_result(self) -> Self::Result;
}

impl ErrorCollector<ErrorGuaranteed> for Option<ErrorGuaranteed> {
    type Result = Result<(), ErrorGuaranteed>;

    fn collect_err(&mut self, err: ErrorGuaranteed) {
        *self = Some(err).or(*self);
    }

    fn into_result(self) -> Self::Result {
        if let Some(err) = self {
            Err(err)
        } else {
            Ok(())
        }
    }
}

pub trait ResultExt<T, E> {
    fn collect_err(self, collector: &mut impl ErrorCollector<E>);

    #[track_caller]
    fn emit<'a>(self, emitter: &'a impl ErrorEmitter) -> Result<T, ErrorGuaranteed>
    where
        E: Diagnostic<'a>;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn collect_err(self, collector: &mut impl ErrorCollector<E>) {
        if let Err(err) = self {
            collector.collect_err(err);
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
