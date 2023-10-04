#[flux::sig(fn() -> [i32{v : v > 0}; 2])]
pub fn array00() -> [i32; 2] {
    [0, 1] //~ ERROR refinement type
}

#[flux::sig(fn() -> i32{v : v > 100})]
pub fn write() -> i32 {
    let bytes: [i32; 2] = [10, 20];
    bytes[0] + bytes[1] //~ ERROR refinement type
}

#[allow(unconditional_panic)]
#[flux::sig(fn() -> i32)]
pub fn write2() -> i32 {
    let bytes: [i32; 2] = [10, 20];
    bytes[100] //~ ERROR assertion might fail
}
