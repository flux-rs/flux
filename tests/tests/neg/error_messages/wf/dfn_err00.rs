#![flux::defs {
    fn nat(x: int) -> bool { 0 <= x }
    fn bat(x: int) -> int  { 0 <= x } //~ ERROR mismatched sorts
}]
