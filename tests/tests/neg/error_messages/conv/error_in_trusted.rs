struct MyStruct {}

// Check we report error during conv in a trusted function
#[flux::trusted]
#[flux::sig(fn(x: MyStruct<i32>))] //~ ERROR this struct takes 0 generic
fn test_get(x: MyStruct) {}
