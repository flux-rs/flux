use rustc_middle::mir::Body;

#[derive(Debug)]
pub enum Annotation {
    Ty(String),
}

#[derive(Debug)]
pub struct Function<'tcx> {
    body: Body<'tcx>,
    anns: Vec<Annotation>,
}

impl<'tcx> Function<'tcx> {
    pub fn new(body: Body<'tcx>, anns: Vec<Annotation>) -> Self {
        Self { body, anns }
    }
}
