use crate::SemiGroup;

#[derive(Debug)]
pub struct ErrorReported;

impl SemiGroup for ErrorReported {
    fn append(self, _: Self) -> Self {
        ErrorReported
    }
}
