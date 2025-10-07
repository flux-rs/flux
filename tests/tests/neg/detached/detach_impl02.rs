#![allow(unused)]

use flux_rs::attrs::*;

enum Nat {
    Zero,
    Succ(Box<Nat>),
}

impl Nat {
    fn zero() -> Self {
        Nat::Zero
    }

    fn succ(n: Self) -> Self {
        Nat::Succ(Box::new(n))
    }
}

impl From<usize> for Nat {
    fn from(val: usize) -> Self {
        if val == 0 { Nat::zero() } else { Nat::succ(Nat::from(val - 1)) }
    }
}

impl From<Nat> for usize {
    fn from(val: Nat) -> Self {
        match val {
            Nat::Zero => 0,
            Nat::Succ(n) => 1 + Self::from(*n),
        }
    }
}

// --------------------------------------------------------------------------------------

#[spec(fn () -> Nat[3])]
fn test_a() -> Nat {
    Nat::succ(Nat::succ(Nat::succ(Nat::zero())))
}

#[spec(fn () -> Nat[3])]
fn test_b() -> Nat {
    let n: usize = 3;
    Nat::from(3)
}

#[spec(fn () -> usize[4])]
fn test_c() -> usize {
    let n3 = test_b();
    usize::from(n3)
} //~ ERROR refinement type

// --------------------------------------------------------------------------------------

#[flux::specs {

    #[refined_by(n: int)]
    #[invariant(0 <= n)]
    enum Nat {
      Zero               -> Nat[0],
      Succ(Box<Nat[@n]>) -> Nat[n + 1],
    }

    impl Nat {
      fn zero() -> Nat[0];
      fn succ(n:Nat) -> Nat[n+1];
    }

    impl std::convert::From<usize> for Nat {
      fn from(n: usize) -> Nat[n];
    }

    impl std::convert::From<Nat> for usize {
      fn from(n: Nat) -> usize[n];
    }
}]
const _: () = ();
