import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestEnumer2
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestEnumer2Qualifs

@[qualif]
def EqTrue (next_s₀ : Prop) : Prop :=
  next_s₀

@[qualif]
def EqFalse (next_s₀ : Prop) : Prop :=
  (¬next_s₀)

@[qualif]
def EqZero (next_s₀ : Int) : Prop :=
  (next_s₀ = 0)

@[qualif]
def GtZero (next_s₀ : Int) : Prop :=
  (next_s₀ > 0)

@[qualif]
def GeZero (next_s₀ : Int) : Prop :=
  (next_s₀ ≥ 0)

@[qualif]
def LtZero (next_s₀ : Int) : Prop :=
  (next_s₀ < 0)

@[qualif]
def LeZero (next_s₀ : Int) : Prop :=
  (next_s₀ ≤ 0)

@[qualif]
def Eq (next_s₀ : Int) (next_s₁ : Int) : Prop :=
  (next_s₀ = next_s₁)

@[qualif]
def Gt (next_s₀ : Int) (next_s₁ : Int) : Prop :=
  (next_s₀ > next_s₁)

@[qualif]
def Ge (next_s₀ : Int) (next_s₁ : Int) : Prop :=
  (next_s₀ ≥ next_s₁)

@[qualif]
def Lt (next_s₀ : Int) (next_s₁ : Int) : Prop :=
  (next_s₀ < next_s₁)

@[qualif]
def Le (next_s₀ : Int) (next_s₁ : Int) : Prop :=
  (next_s₀ ≤ next_s₁)

@[qualif]
def Le1 (next_s₀ : Int) (next_s₁ : Int) : Prop :=
  (next_s₀ ≤ (next_s₁ - 1))

end TestEnumer2Qualifs

open TestEnumer2Qualifs

set_option maxHeartbeats 5000000
#time def TestEnumer2_proof : TestEnumer2 := by
  unfold TestEnumer2
  solve_fixpoint_combo

end F
