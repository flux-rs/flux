import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestAndThenNoneInput
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestAndThenNoneInputQualifs

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

end TestAndThenNoneInputQualifs

open TestAndThenNoneInputQualifs

set_option maxHeartbeats 5000000
def TestAndThenNoneInput_proof : TestAndThenNoneInput := by
  unfold TestAndThenNoneInput
  solve_fixpoint_combo

end F
