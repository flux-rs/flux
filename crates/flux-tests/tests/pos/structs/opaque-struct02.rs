#[flux::opaque]
struct Ptr<T> {
    data: *mut T,
}
