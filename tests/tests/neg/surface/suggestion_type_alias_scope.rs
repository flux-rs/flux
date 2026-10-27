// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 1
// suggestion: fn(crate::types::Count[@x])
// The input must resolve; the replacement must use Renamed or a qualified path.
#![flux::opts(check_overflow = "strict")]

mod types {
    #[flux::refined_by(value: int)]
    pub struct Count {
        #[flux::field(u32[value])]
        pub value: u32,
    }
}

mod target {
    use crate::types::Count as Renamed;

    #[flux::sig(fn(Renamed) -> u32)]
    pub fn increment(x: Renamed) -> u32 {
        x.value + 1 //~ ERROR arithmetic operation may overflow
    }
}
