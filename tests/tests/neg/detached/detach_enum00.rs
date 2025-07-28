pub enum Nat {
    Zero,
    Succ(Box<Nat>),
}

pub fn zero() -> Nat {
    Nat::Zero //~ ERROR refinement type
}

pub fn succ(n: Nat) -> Nat {
    Nat::Succ(Box::new(n))
}

pub fn from_usize(n: usize) -> Nat {
    if n == 0 { Nat::Zero } else { succ(from_usize(n - 1)) }
}

#[flux::specs {

    #[refined_by(n: int)]
    #[invariant(0 <= n)]
    enum Nat {
      Zero               -> Nat[0],
      Succ(Box<Nat[@n]>) -> Nat[n+1],
    }

    fn zero() -> Nat[1];

    fn succ(n:Nat) -> Nat[n+1];

    fn from_usize(n:usize) -> Nat[n];
}]
const _: () = ();
