// The `#` wildcard marker is only meaningful on a qualifier parameter, so it is a syntax error
// anywhere else a refinement parameter can appear.

#![flux::defs {
    fn dbl(x #: int) -> int { x + x } //~ ERROR syntax error
}]
