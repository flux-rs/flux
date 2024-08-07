#[flux::sig(fn (&str["cat"]))]
fn require_cat(_x: &str) {}

pub fn test_cat() {
    require_cat("cat");
    require_cat("dog"); //~ ERROR refinement type
}

// #[flux::sig(fn (&usize[10]))]
// fn require_ten(_z: &usize) {}

// pub fn test_ten() {
//     require_ten(&11); //~ ERROR refinement type
// }

// #[flux::sig(fn (&str[@a], &{str[@b] | a == b}))]
// fn require_eq(_x: &str, _y: &str) {}

// pub fn test_eq() {
//     require_eq("a", "a");
//     require_eq("a", "b"); //~ ERROR refinement type
// }
