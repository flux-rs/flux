import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestEnumerate1
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestEnumerate1Qualifs

@[qualif]
def EqTrue (n₀ : Prop) : Prop :=
  n₀

@[qualif]
def EqFalse (n₀ : Prop) : Prop :=
  (¬n₀)

@[qualif]
def EqZero (n₀ : Int) : Prop :=
  (n₀ = 0)

@[qualif]
def GtZero (n₀ : Int) : Prop :=
  (n₀ > 0)

@[qualif]
def GeZero (n₀ : Int) : Prop :=
  (n₀ ≥ 0)

@[qualif]
def LtZero (n₀ : Int) : Prop :=
  (n₀ < 0)

@[qualif]
def LeZero (n₀ : Int) : Prop :=
  (n₀ ≤ 0)

@[qualif]
def Eq (n₀ : Int) (next_s₀ : Int) : Prop :=
  (n₀ = next_s₀)

@[qualif]
def Gt (n₀ : Int) (next_s₀ : Int) : Prop :=
  (n₀ > next_s₀)

@[qualif]
def Ge (n₀ : Int) (next_s₀ : Int) : Prop :=
  (n₀ ≥ next_s₀)

@[qualif]
def Lt (n₀ : Int) (next_s₀ : Int) : Prop :=
  (n₀ < next_s₀)

@[qualif]
def Le (n₀ : Int) (next_s₀ : Int) : Prop :=
  (n₀ ≤ next_s₀)

@[qualif]
def Le1 (n₀ : Int) (next_s₀ : Int) : Prop :=
  (n₀ ≤ (next_s₀ - 1))

end TestEnumerate1Qualifs

open TestEnumerate1Qualifs

set_option maxHeartbeats 5000000
def TestEnumerate1_proof : TestEnumerate1 := by
  unfold TestEnumerate1
  solve_fixpoint_combo

end F
