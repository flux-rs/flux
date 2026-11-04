//@run-rustfix
//@normalize-stderr-test: "(?s).*" -> ""
//@rustfix-only-machine-applicable
//@compile-flags: -Fsuggestions=true -Ffix-suggestions
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
        x.value + 1
    }
}
