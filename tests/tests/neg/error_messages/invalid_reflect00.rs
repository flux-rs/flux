// #[flux::reflect]
// pub enum State {
//     #[flux::variant(State[0])] //~ ERROR invalid variant for reflected enum
//     On,
//     #[flux::variant(State[1])] //~ ERROR invalid variant for reflected enum
//     Off,
// }

#[flux::reflect]
#[flux::refined_by(val : int )]
pub enum Day {
    Sat,
    Sun,
}
