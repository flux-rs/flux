const A: &[i32] = &[0];
const B: &[i32] = &[1];

fn test() -> Vec<&'static i32> {
    A.iter().chain(B).collect()
}
