pub struct GrantKernelData<'a> {
    upcall: &'a usize,
}

impl<'a> GrantKernelData<'a> {
    fn new(upcall: &'a usize) -> GrantKernelData<'a> {
        Self { upcall }
    }
}
