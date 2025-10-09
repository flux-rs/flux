use flux_rs::attrs::*;

pub enum Nat {
    Zero,
    Succ(Box<Nat>),
}

impl Nat {
    fn zero() -> Self {
        //~^ ERROR multiple specifications
        Nat::Zero
    }
}

impl Nat {
    fn succ(n: Self) -> Self {
        Nat::Succ(Box::new(n))
    }
}

// --------------------------------------------------------------------------------------

#[spec(fn () -> Nat[0])]
pub fn test_a() -> Nat {
    Nat::zero()
}

#[spec(fn () -> Nat[3])]
pub fn test_b() -> Nat {
    Nat::succ(Nat::succ(Nat::succ(Nat::zero())))
}

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

    }

    impl Nat {

        fn zero() -> Nat[0];

        fn succ(n:Nat) -> Nat[n+1];

    }
}]
const _: () = ();
