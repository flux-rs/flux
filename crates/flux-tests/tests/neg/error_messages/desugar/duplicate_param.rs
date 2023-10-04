#[flux::sig(fn(xanadu:i32,











    xanadu:i32))] //~ ERROR the name `xanadu` is already used as a parameter
pub fn test00(_x: i32, _y: i32) {}
