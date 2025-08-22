#![feature(trait_alias)]

pub trait Pointee {
    type Metadata;
}

pub trait Thin = Pointee<Metadata = ()>;

pub const fn test(data_pointer: *const impl Thin) {}
