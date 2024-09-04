pub trait RsaKey {
    fn map_modulus(&self, closure: &dyn Fn(&[u8]));
}
