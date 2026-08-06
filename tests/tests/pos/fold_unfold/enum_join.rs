// Joining a branch that borrows into an enum variant with one that doesn't. The join can only fold
// `e` back — the other branch has no way to reach the `A` variant — but the field is blocked by the
// borrow that outlives the join, so the fold has to use the borrow's guard as the type of the field
// and leave the whole enum blocked.

enum E {
    A(usize),
    B,
}

fn test00(mut e: E, mut z: usize) {
    let r = if let E::A(ref mut x) = e { x } else { &mut z };
    *r = 1;
}

#[flux::refined_by(n: int)]
enum F {
    #[flux::variant((usize[@n]) -> F[n])]
    A(usize),
    #[flux::variant(F[0])]
    B,
}

// same, but the field is refined, so folding has to bind the guard's variable in the result
fn test01(mut e: F, mut z: usize) {
    let r = if let F::A(ref mut x) = e { x } else { &mut z };
    *r = 1;
}
