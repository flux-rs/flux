use liquid_rust_fixpoint::Emit;
use liquid_rust_mir::FuncId;
use liquid_rust_ty::LocalVariable;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct GlobVariable(pub(crate) FuncId, pub(crate) LocalVariable);

impl GlobVariable {
    pub(crate) fn mapper(func_id: FuncId) -> impl Fn(LocalVariable) -> Self + Copy {
        move |var| Self(func_id, var)
    }
}

impl Emit for GlobVariable {
    fn emit<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        write!(writer, "{}_{}", self.0, self.1)
    }
}
