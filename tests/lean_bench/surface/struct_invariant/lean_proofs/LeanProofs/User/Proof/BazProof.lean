import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Baz
open Classical

namespace F

namespace BazQualifs

@[qualif]
def EqTrue (s₀ : Prop) : Prop :=
  s₀

@[qualif]
def EqFalse (s₀ : Prop) : Prop :=
  (¬s₀)

@[qualif]
def EqZero (s₀ : Int) : Prop :=
  (s₀ = 0)

@[qualif]
def GtZero (s₀ : Int) : Prop :=
  (s₀ > 0)

@[qualif]
def GeZero (s₀ : Int) : Prop :=
  (s₀ ≥ 0)

@[qualif]
def LtZero (s₀ : Int) : Prop :=
  (s₀ < 0)

@[qualif]
def LeZero (s₀ : Int) : Prop :=
  (s₀ ≤ 0)

@[qualif]
def Eq (s₀ : Int) (a'₁ : Int) : Prop :=
  (s₀ = a'₁)

@[qualif]
def Gt (s₀ : Int) (a'₁ : Int) : Prop :=
  (s₀ > a'₁)

@[qualif]
def Ge (s₀ : Int) (a'₁ : Int) : Prop :=
  (s₀ ≥ a'₁)

@[qualif]
def Lt (s₀ : Int) (a'₁ : Int) : Prop :=
  (s₀ < a'₁)

@[qualif]
def Le (s₀ : Int) (a'₁ : Int) : Prop :=
  (s₀ ≤ a'₁)

@[qualif]
def Le1 (s₀ : Int) (a'₁ : Int) : Prop :=
  (s₀ ≤ (a'₁ - 1))

end BazQualifs

open BazQualifs

set_option maxHeartbeats 5000000
def Baz_proof : Baz := by
  unfold Baz
  try solve_fixpoint

end F
