import LeanFixpoint
import Surface.Iter02.Flux.Prelude
import Surface.Iter02.Flux.VC.TestEnumer3
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestEnumer3Qualifs

@[qualif]
def EqTrue (e₀ : Prop) : Prop :=
  e₀

@[qualif]
def EqFalse (e₀ : Prop) : Prop :=
  (¬e₀)

@[qualif]
def EqZero (e₀ : Int) : Prop :=
  (e₀ = 0)

@[qualif]
def GtZero (e₀ : Int) : Prop :=
  (e₀ > 0)

@[qualif]
def GeZero (e₀ : Int) : Prop :=
  (e₀ ≥ 0)

@[qualif]
def LtZero (e₀ : Int) : Prop :=
  (e₀ < 0)

@[qualif]
def LeZero (e₀ : Int) : Prop :=
  (e₀ ≤ 0)

@[qualif]
def Eq (e₀ : Int) (next_s₀ : Int) : Prop :=
  (e₀ = next_s₀)

@[qualif]
def Gt (e₀ : Int) (next_s₀ : Int) : Prop :=
  (e₀ > next_s₀)

@[qualif]
def Ge (e₀ : Int) (next_s₀ : Int) : Prop :=
  (e₀ ≥ next_s₀)

@[qualif]
def Lt (e₀ : Int) (next_s₀ : Int) : Prop :=
  (e₀ < next_s₀)

@[qualif]
def Le (e₀ : Int) (next_s₀ : Int) : Prop :=
  (e₀ ≤ next_s₀)

@[qualif]
def Le1 (e₀ : Int) (next_s₀ : Int) : Prop :=
  (e₀ ≤ (next_s₀ - 1))

end TestEnumer3Qualifs

open TestEnumer3Qualifs

set_option maxHeartbeats 5000000
#time def TestEnumer3_proof : TestEnumer3 := by
  unfold TestEnumer3
  solve_fixpoint_combo

end F
