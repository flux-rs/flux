#[flux::reflect]
pub enum Day {
    Sat(i32), //~ ERROR reflected enum variants cannot have any fields
    Sun,
}
