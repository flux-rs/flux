pub struct Packet<'a>(&'a [u8]);

pub struct Nested {
    callback: fn(fn(Packet) -> Packet) -> fn(Packet) -> Packet,
}

impl Nested {
    pub fn new(callback: fn(fn(Packet) -> Packet) -> fn(Packet) -> Packet) -> Self {
        Self { callback }
    }
}
