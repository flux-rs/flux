fn test(x: i32, y: i32) {
    let r: (i32, &i32);
    let r = if true { (0, &x) } else { (1, &y) };
}
