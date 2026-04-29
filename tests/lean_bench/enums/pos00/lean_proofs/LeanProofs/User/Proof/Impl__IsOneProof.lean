import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__IsOne
open Classical

namespace F

namespace ImplIsOneQualifs

@[qualif]
def EqTrue (n₁ : Prop) : Prop :=
  n₁

@[qualif]
def EqFalse (n₁ : Prop) : Prop :=
  (¬n₁)

@[qualif]
def EqZero (n₁ : Int) : Prop :=
  (n₁ = 0)

@[qualif]
def GtZero (n₁ : Int) : Prop :=
  (n₁ > 0)

@[qualif]
def GeZero (n₁ : Int) : Prop :=
  (n₁ ≥ 0)

@[qualif]
def LtZero (n₁ : Int) : Prop :=
  (n₁ < 0)

@[qualif]
def LeZero (n₁ : Int) : Prop :=
  (n₁ ≤ 0)

@[qualif]
def Eq (n₁ : Int) (n₂ : Int) : Prop :=
  (n₁ = n₂)

@[qualif]
def Gt (n₁ : Int) (n₂ : Int) : Prop :=
  (n₁ > n₂)

@[qualif]
def Ge (n₁ : Int) (n₂ : Int) : Prop :=
  (n₁ ≥ n₂)

@[qualif]
def Lt (n₁ : Int) (n₂ : Int) : Prop :=
  (n₁ < n₂)

@[qualif]
def Le (n₁ : Int) (n₂ : Int) : Prop :=
  (n₁ ≤ n₂)

@[qualif]
def Le1 (n₁ : Int) (n₂ : Int) : Prop :=
  (n₁ ≤ (n₂ - 1))

end ImplIsOneQualifs

open ImplIsOneQualifs

def Impl__IsOne_proof : Impl__IsOne := by
  unfold Impl__IsOne
  try solve_fixpoint

end F
