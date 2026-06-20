#![flux::defs(
    fn silly_prop() -> bool {
        forall b in 0..5 { b }  //~ ERROR mismatched sorts
    }
)]

#[flux::spec(fn() ensures silly_prop())]
fn test1() {}
