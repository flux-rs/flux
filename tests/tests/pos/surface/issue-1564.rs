use std::{fs::File, io::Read};

fn read_example(file: &mut File) {
    let mut buf = [0u8; 4096];
    let _ = file.read_exact(&mut buf);
}
