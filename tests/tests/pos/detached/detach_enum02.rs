pub mod wrapper {

    pub enum Nat {
        Zero,
        Succ(Box<Nat>),
    }

    pub fn zero() -> Nat {
        Nat::Zero
    }

    //
    #[flux::specs {
        #[refined_by(n: int)]
        #[invariant(0 <= n)]
        enum Nat {
          Zero               -> Nat[0],
          Succ(Box<Nat[@n]>) -> Nat[n+1],
        }

        fn zero() -> Nat[0];

    }]
    const _: () = ();
}
