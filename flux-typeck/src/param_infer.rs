use flux_middle::rty::{subst::FVarSubst, Name};

#[derive(Debug, Eq, PartialEq)]
pub struct InferenceError(pub String);

pub fn check_inference(
    subst: &FVarSubst,
    params: impl Iterator<Item = Name>,
) -> Result<(), InferenceError> {
    for name in params {
        if !subst.contains(name) {
            return Err(InferenceError(format!("{name:?}")));
        }
    }
    Ok(())
}
