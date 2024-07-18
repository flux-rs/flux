pub fn foo(x: Vec<i32>) {
    let _blah = x.iter().find(|&&x| x == 0);
}
