pub struct TracerPacket<'a> {
    pub buffer: &'a [u8],
}

pub struct Tracer {
    writer: fn(TracerPacket),
}

impl Tracer {
    pub fn new(writer: fn(TracerPacket)) -> Tracer {
        Tracer { writer }
    }
}
