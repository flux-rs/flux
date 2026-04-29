import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__Set
open Classical

namespace F

namespace ImplSetQualifs

@[qualif]
def EqTrue (v₀ : Prop) : Prop :=
  v₀

@[qualif]
def EqFalse (v₀ : Prop) : Prop :=
  (¬v₀)

@[qualif]
def EqZero (v₀ : Int) : Prop :=
  (v₀ = 0)

@[qualif]
def GtZero (v₀ : Int) : Prop :=
  (v₀ > 0)

@[qualif]
def GeZero (v₀ : Int) : Prop :=
  (v₀ ≥ 0)

@[qualif]
def LtZero (v₀ : Int) : Prop :=
  (v₀ < 0)

@[qualif]
def LeZero (v₀ : Int) : Prop :=
  (v₀ ≤ 0)

@[qualif]
def Eq (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ = a'₁)

@[qualif]
def Gt (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ > a'₁)

@[qualif]
def Ge (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ ≥ a'₁)

@[qualif]
def Lt (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ < a'₁)

@[qualif]
def Le (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ ≤ a'₁)

@[qualif]
def Le1 (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ ≤ (a'₁ - 1))

end ImplSetQualifs

open ImplSetQualifs

def Impl__Set_proof : Impl__Set := by
  unfold Impl__Set
  intros N M i j v h1 h2 h3 h4 h5
  apply @Int.lt_of_lt_of_le _ ((N - 1) * M + M)
  · have : i * M ≤ (N - 1) * M := by
      apply Int.mul_le_mul
        <;> omega
    grind
  · grind
  -- try solve_fixpoint

end F
