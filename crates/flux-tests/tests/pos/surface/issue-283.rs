#[flux::sig(fn(x: std::primitive::i32) -> std::primitive::i32[x + 1])]
fn test00(x: std::primitive::i32) -> std::primitive::i32 {
    x + 1
}
