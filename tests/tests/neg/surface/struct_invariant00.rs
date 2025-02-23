#[flux::invariant(n > 10)]
#[flux::refined_by(n : int)]
pub struct MPUGOOD {
    #[flux::field(i32[n])]
    pub fld: i32,
}

pub fn bar(z: i32) -> MPUGOOD {
    let fld = z;
    MPUGOOD { fld } //~ ERROR refinement type
}
