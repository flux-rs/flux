use flux_rs::attrs::*;

#[spec(fn () -> usize{v: 10 <= v})]
fn random() -> usize {
    10
}

fn test_return() {
    let banana = random();
    flux_rs::assert(10 <= banana);
}

fn test_immut(caesar: &Salad) {
    let fs = caesar.fruits;
    let ns = caesar.nuts;
    flux_rs::assert(fs > ns);
}

fn test_tuple(z: (usize, bool)) -> usize {
    let (i, b) = z;
    if b { i + 1 } else { i }
}

fn test_array(z: &[usize]) -> usize {
    if z.len() > 10 {
        let val0 = z[0];
        let val1 = z[1];
        val0 + val1
    } else {
        12
    }
}
