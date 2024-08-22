pub fn test() {
    let mut vec = Vec::new();
    let thing = Some(1);
    thing.map(|x| vec.push(x));
}
