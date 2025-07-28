enum Nat {
    Zero,
    Succ(Box<Nat>),
}

fn zero() -> Nat {
    Nat::Zero
}

fn succ(n: Nat) -> Nat {
    Nat::Succ(Box::new(n))
}

fn from_usize(n: usize) -> Nat {
    if n == 0 { zero() } else { succ(from_usize(n - 1)) }
}

#[flux::specs {

    enum Nat
      refined_by(n:int)
      invariant(0 <= n)
    {
      Zero               -> Nat[0],
      Succ(Box<Nat[@n]>) -> Nat[n+1],
    }

    fn zero() -> Nat[0];

    fn succ(n:Nat) -> Nat[n+1];

    fn from_usize(n:usize) -> Nat[n];
}]
const _: () = ();
