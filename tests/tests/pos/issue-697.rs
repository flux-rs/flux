pub fn test00<F>(f: F)
where
    F: Fn(u32) -> bool,
{
    if f(0) {
        println!("Hello");
    }
}

pub fn test01(f: impl Fn(u32) -> bool) {
    if f(0) {
        println!("Hello");
    }
}
