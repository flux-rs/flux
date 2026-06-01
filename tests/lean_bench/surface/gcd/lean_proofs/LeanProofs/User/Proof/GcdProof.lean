import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Gcd
open Classical

namespace F

namespace GcdQualifs

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
def Eq (v₀ : Int) (v₁ : Int) : Prop :=
  (v₀ = v₁)

@[qualif]
def Gt (v₀ : Int) (v₁ : Int) : Prop :=
  (v₀ > v₁)

@[qualif]
def Ge (v₀ : Int) (v₁ : Int) : Prop :=
  (v₀ ≥ v₁)

@[qualif]
def Lt (v₀ : Int) (v₁ : Int) : Prop :=
  (v₀ < v₁)

@[qualif]
def Le (v₀ : Int) (v₁ : Int) : Prop :=
  (v₀ ≤ v₁)

@[qualif]
def Le1 (v₀ : Int) (v₁ : Int) : Prop :=
  (v₀ ≤ (v₁ - 1))

end GcdQualifs

open GcdQualifs

set_option maxHeartbeats 5000000
def Gcd_proof : Gcd := by
  unfold Gcd
  try solve_fixpoint

end F
