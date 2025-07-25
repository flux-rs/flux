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

#[refined_by(n:int)]
struct Usize(#[field(usize[n])] usize);

impl From<Usize> for Nat {
    fn from(val: Usize) -> Self {
        let n = val.0;
        if n == 0 { Nat::zero() } else { Nat::succ(Nat::from(Usize(n - 1))) }
    }
}

impl From<Nat> for Usize {
    fn from(val: Nat) -> Self {
        match val {
            Nat::Zero => Usize(0),
            Nat::Succ(n) => Usize(1 + Self::from(*n).0),
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
    let n = Usize(3);
    Nat::from(n)
}

#[spec(fn () -> Usize[3])]
fn test_c() -> Usize {
    let n3 = test_b();
    Usize::from(n3)
}

// --------------------------------------------------------------------------------------

#[flux::specs {

    enum Nat[n:int]
      invariant(0 <= n)
    {
      Zero               -> Nat[0],
      Succ(Box<Nat[@n]>) -> Nat[n + 1],
    }

    impl Nat {
      fn zero() -> Nat[0];
      fn succ(n:Nat) -> Nat[n+1];
    }

    impl From<Usize> for Nat {
      fn from(n: Usize) -> Nat[n];
    }

    impl From<Nat> for Usize {
      fn from(n: Nat) -> Usize[n];
    }
}]
const _: () = ();
