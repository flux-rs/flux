use liquid_rust_common::errors::ErrorReported;
use rustc_session::{Session, SessionDiagnostic};

pub(crate) struct Diagnostics<'tcx> {
    sess: &'tcx Session,
    errors: usize,
}

impl Diagnostics<'_> {
    pub fn new(sess: &Session) -> Diagnostics {
        Diagnostics { sess, errors: 0 }
    }

    pub fn raise<T>(&mut self) -> Result<T, ErrorReported> {
        assert!(self.errors > 0);
        self.errors = 0;
        Err(ErrorReported)
    }

    // fn raise_if_errors(&mut self) -> Result<(), ErrorReported> {
    //     if self.errors > 0 {
    //         self.errors = 0;
    //         Err(ErrorReported)
    //     } else {
    //         Ok(())
    //     }
    // }

    pub fn emit_err<'a>(&'a mut self, err: impl SessionDiagnostic<'a>) -> &mut Self {
        self.sess.emit_err(err);
        self.errors += 1;
        self
    }
}

impl Drop for Diagnostics<'_> {
    fn drop(&mut self) {
        assert!(self.errors == 0);
    }
}

pub(crate) mod errors {
    use liquid_rust_syntax::ast;
    use rustc_macros::SessionDiagnostic;
    use rustc_span::{symbol::Ident, Span};

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnsupportedSignature {
        #[message = "unsupported function signature"]
        #[label = "{msg}"]
        pub span: Span,
        pub msg: &'static str,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnresolvedPath {
        #[message = "could not resolve `{path}`"]
        #[label = "failed to resolve `{path}`"]
        pub span: Span,
        pub path: Ident,
    }

    impl UnresolvedPath {
        pub fn new(path: &ast::Path) -> Self {
            Self { span: path.span, path: path.ident }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnresolvedLoc {
        #[message = "cannot find location parameter `{loc}` in this scope"]
        span: Span,
        loc: Ident,
    }

    impl UnresolvedLoc {
        pub fn new(loc: Ident) -> Self {
            Self { span: loc.span, loc }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct DuplicateParam {
        #[message = "the name `{name}` is already used as a parameter"]
        #[label = "already used"]
        span: Span,
        name: Ident,
    }

    impl DuplicateParam {
        pub fn new(name: Ident) -> Self {
            Self { span: name.span, name }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct DesugarError {
        #[message = "cannot desugar this type because {msg}"]
        #[label = "desugar"]
        pub span: Span,
        pub msg: String,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct RefinedTypeParam {
        #[message = "type parameters cannot be refined"]
        #[label = "refined type parameter"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct RefinedFloat {
        #[message = "float cannot be refined"]
        #[label = "refined float"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct InvalidAdt {
        #[message = "ADT without arguments"]
        #[label = "invalid adt"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnresolvedSort {
        #[message = "cannot find sort `{sort}` in this scope"]
        #[label = "not found in this scope"]
        pub span: Span,
        pub sort: Ident,
    }

    impl UnresolvedSort {
        pub fn new(sort: Ident) -> Self {
            Self { span: sort.span, sort }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnresolvedVar {
        #[message = "cannot find value `{var}` in this scope"]
        #[label = "not found in this scope"]
        pub span: Span,
        pub var: Ident,
    }

    impl UnresolvedVar {
        pub fn new(var: Ident) -> Self {
            Self { span: var.span, var }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct IntTooLarge {
        #[message = "integer literal is too large"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnexpectedLiteral {
        #[message = "unexpected literal"]
        pub span: Span,
    }
}
