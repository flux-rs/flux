#![flux::defs {
    fn uif(x: int) -> bool;

    fn not_hidden(x: int) -> bool {
        x > 0
    }

    #[hide]
    fn hidden(x: int) -> bool {
        x > 0
    }
}]

#[flux::reveal(uif)] //~ ERROR cannot reveal uninterpreted function
pub fn reveal_uif() {}

#[flux::reveal(not_hidden)] //~ WARN has no effect
pub fn reveal_not_hidden() {}

#[flux::hide(uif)] //~ WARN has no effect
pub fn hide_uif() {}

#[flux::reveal(hidden)]
pub fn reveal_hidden() {}
