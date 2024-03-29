// Read through box under & ref
#[flux::sig(fn(&Box<i32{v : v >= 0}>) -> i32{v : v > 1})]
pub fn shared_ref_box(x: &Box<i32>) -> i32 {
    **x + 1 //~ ERROR refinement type
}

// Mutate through box under &mut ref
#[flux::sig(fn(&mut Box<i32{v : v >= 0}>))]
pub fn mut_ref_box(x: &mut Box<i32>) {
    **x -= 1; //~ ERROR assignment
}
