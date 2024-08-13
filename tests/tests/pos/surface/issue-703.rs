pub fn gather<I: IntoIterator<Item = i32>>(_inputs: I) {}

pub fn test() {
    gather([1, 2, 3])
}
