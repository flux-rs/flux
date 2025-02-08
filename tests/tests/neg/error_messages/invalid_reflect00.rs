#[flux::reflect]
#[flux::refined_by(val : int )]
pub enum Day {
    //~^ ERROR reflected enum with `refined_by` annotation
    Sat,
    Sun,
}
