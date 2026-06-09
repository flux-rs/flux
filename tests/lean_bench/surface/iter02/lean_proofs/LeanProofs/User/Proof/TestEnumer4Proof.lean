import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestEnumer4
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestEnumer4Qualifs

@[qualif]
def EqTrue (iter₀ : Prop) : Prop :=
  iter₀

@[qualif]
def EqFalse (iter₀ : Prop) : Prop :=
  (¬iter₀)

@[qualif]
def EqZero (iter₀ : Int) : Prop :=
  (iter₀ = 0)

@[qualif]
def GtZero (iter₀ : Int) : Prop :=
  (iter₀ > 0)

@[qualif]
def GeZero (iter₀ : Int) : Prop :=
  (iter₀ ≥ 0)

@[qualif]
def LtZero (iter₀ : Int) : Prop :=
  (iter₀ < 0)

@[qualif]
def LeZero (iter₀ : Int) : Prop :=
  (iter₀ ≤ 0)

@[qualif]
def Eq (iter₀ : Int) (next_s₀ : Int) : Prop :=
  (iter₀ = next_s₀)

@[qualif]
def Gt (iter₀ : Int) (next_s₀ : Int) : Prop :=
  (iter₀ > next_s₀)

@[qualif]
def Ge (iter₀ : Int) (next_s₀ : Int) : Prop :=
  (iter₀ ≥ next_s₀)

@[qualif]
def Lt (iter₀ : Int) (next_s₀ : Int) : Prop :=
  (iter₀ < next_s₀)

@[qualif]
def Le (iter₀ : Int) (next_s₀ : Int) : Prop :=
  (iter₀ ≤ next_s₀)

@[qualif]
def Le1 (iter₀ : Int) (next_s₀ : Int) : Prop :=
  (iter₀ ≤ (next_s₀ - 1))

end TestEnumer4Qualifs

open TestEnumer4Qualifs

set_option maxHeartbeats 5000000
def TestEnumer4_proof : TestEnumer4 := by
  unfold TestEnumer4
  try solve_fixpoint

end F
