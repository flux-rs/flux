#![feature(register_tool)]
#![register_tool(flux)]

pub fn from_array<const N: usize>(items: [i32; N]) -> Vec<i32> {
    items.to_vec()
}

fn test() -> Vec<i32> {
    from_array([1, 2, 3])
}
