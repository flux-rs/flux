#[flux::sig(fn(xanadu:i32,











    xanadu:i32))] //~ ERROR identifier `xanadu` is bound more than once
pub fn test00(_x: i32, _y: i32) {}
