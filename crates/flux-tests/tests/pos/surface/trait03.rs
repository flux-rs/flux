//! Normalization with lifetimes

struct S<'a> {
    x: &'a i32,
}

trait Trait {
    type Item;
    fn method(&self) -> <Self as Trait>::Item;
}

impl<'a> Trait for S<'a> {
    type Item = &'a i32;

    fn method(&self) -> <Self as Trait>::Item {
        self.x
    }
}

fn test01(x: S) {
    let _ = x.method();
}

fn test02(v: Vec<i32>) {
    let mut i = v.iter().rev();
    let _ = i.next();
}
