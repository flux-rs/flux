#[flux::reflect]
pub enum Day {
    Sat(i32), //~ ERROR reflected enum variants cannot have any fields
    Sun,
}

#[flux::sig(fn (Day[Day::Sat]) -> i32[10])]
pub fn test(x: Day) -> i32 {
    match x {
        Day::Sat(x) => x,
        Day::Sun => 0,
    }
}
