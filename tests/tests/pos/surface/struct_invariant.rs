#[flux::invariant(n > 10)]
#[flux::refined_by(n : int)]
pub struct MPUGOOD {
    #[flux::field(i32[n])]
    pub fld: i32,
}

#[flux::sig(fn (z:i32{99 < z} ) -> MPUGOOD[z])]
pub fn bar(z: i32) -> MPUGOOD {
    let fld = z;
    MPUGOOD { fld }
}

#[flux::sig(fn (MPUGOOD) -> i32{v: 9 < v})]
pub fn baz(s: MPUGOOD) -> i32 {
    s.fld
}
