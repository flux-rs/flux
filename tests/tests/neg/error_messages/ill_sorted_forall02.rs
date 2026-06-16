#![flux::defs(
    fn silly_prop() -> bool {
        forall i in 0..5 { true }   //~ ERROR bounded quantification
    }

    fn billy_prop() -> bool {
        forall i:bool in 0..5 { true }   //~ ERROR bounded quantification
    }

)]

#[flux::spec(fn() ensures silly_prop())]
fn test_silly() {}

#[flux::spec(fn() ensures billy_prop())]
fn test_billy() {}
