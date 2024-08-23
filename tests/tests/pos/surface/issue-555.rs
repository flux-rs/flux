const A: &[&str] = &["A"];
const B: &[&str] = &["B"];

fn test() -> Vec<&'static str> {
    A.iter().chain(B).copied().collect()
}
