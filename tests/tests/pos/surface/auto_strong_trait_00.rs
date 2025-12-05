pub trait CopyOrErr {
    fn foo(&mut self, src: &Self) -> Result<(), ()>;
}

impl CopyOrErr for [u8] {
    fn foo(&mut self, src: &Self) -> Result<(), ()> {
        Ok(())
    }
}
