#![flux::defs(
    fn billy_prop() -> bool {
        forall i:bool in 0..5 { true }   //~ ERROR bounded quantification
    }

)]

#[flux::spec(fn() ensures billy_prop())]
fn test_billy() {}
