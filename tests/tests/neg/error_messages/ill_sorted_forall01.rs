#![flux::defs(
    fn silly_prop() -> bool {
        forall b in 0..5 { b }  //~ ERROR bounded quantification requires
    }
)]

#[flux::spec(fn() ensures silly_prop())]
fn test1() {}
