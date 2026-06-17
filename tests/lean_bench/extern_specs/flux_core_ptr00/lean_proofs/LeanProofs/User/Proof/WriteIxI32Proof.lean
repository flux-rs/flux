import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WriteIxI32
open Classical
set_option linter.unusedVariables false


namespace F

namespace WriteIxI32Qualifs

@[qualif]
def EqTrue (value₀ : Prop) : Prop :=
  value₀

@[qualif]
def EqFalse (value₀ : Prop) : Prop :=
  (¬value₀)

@[qualif]
def EqZero (value₀ : Int) : Prop :=
  (value₀ = 0)

@[qualif]
def GtZero (value₀ : Int) : Prop :=
  (value₀ > 0)

@[qualif]
def GeZero (value₀ : Int) : Prop :=
  (value₀ ≥ 0)

@[qualif]
def LtZero (value₀ : Int) : Prop :=
  (value₀ < 0)

@[qualif]
def LeZero (value₀ : Int) : Prop :=
  (value₀ ≤ 0)

@[qualif]
def Eq (value₀ : Int) (a'₁ : Int) : Prop :=
  (value₀ = a'₁)

@[qualif]
def Gt (value₀ : Int) (a'₁ : Int) : Prop :=
  (value₀ > a'₁)

@[qualif]
def Ge (value₀ : Int) (a'₁ : Int) : Prop :=
  (value₀ ≥ a'₁)

@[qualif]
def Lt (value₀ : Int) (a'₁ : Int) : Prop :=
  (value₀ < a'₁)

@[qualif]
def Le (value₀ : Int) (a'₁ : Int) : Prop :=
  (value₀ ≤ a'₁)

@[qualif]
def Le1 (value₀ : Int) (a'₁ : Int) : Prop :=
  (value₀ ≤ (a'₁ - 1))

end WriteIxI32Qualifs

open WriteIxI32Qualifs

set_option maxHeartbeats 5000000
#time def WriteIxI32_proof : WriteIxI32 := by
  unfold WriteIxI32
  solve_fixpoint_combo

end F
