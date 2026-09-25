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

    #[flux::sig(fn(Count[@x]) -> u32 requires x.value + 1 <= 4294967295)]
    pub fn increment(x: Renamed) -> u32 {
        x.value + 1
    }
}
