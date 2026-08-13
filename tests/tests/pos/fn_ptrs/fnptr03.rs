// Regression test for https://github.com/flux-rs/flux/issues/1718
// ICE: assertion `left == right` failed when a fn-pointer type whose argument has a lifetime
// is written once as a struct field and once as a function parameter (possibly with a name).

pub struct TracerPacket<'a> {
    pub buffer: &'a [u8],
}

pub struct Tracer {
    writer: fn(TracerPacket),
}

impl Tracer {
    pub fn new(writer: fn(packet: TracerPacket)) -> Tracer {
        Tracer { writer }
    }
}
