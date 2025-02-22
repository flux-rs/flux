#![feature(extern_types)]

extern "C" {
    type A;

    fn create() -> *const A;
    fn take(x: *const A);
}

fn test() {
    unsafe {
        let x = create();
        take(x);
    }
}