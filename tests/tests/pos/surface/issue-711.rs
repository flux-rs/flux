fn test01(parts: Vec<i32>) -> i32 {
    parts.iter().rev().fold(0, |acc, part| {
        acc + part 
    })
}
