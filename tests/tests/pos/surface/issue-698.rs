pub trait ClientVerify<const L: usize> {
    fn verification_done(&self);
}

pub trait DigestVerify<const L: usize> {
    fn set_verify_client(&self, client: &dyn ClientVerify<L>);
}
