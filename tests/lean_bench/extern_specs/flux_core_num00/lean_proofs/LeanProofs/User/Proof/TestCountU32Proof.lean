import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestCountU32
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestCountU32Qualifs

@[qualif]
def EqTrue (x₀ : Prop) : Prop :=
  x₀

@[qualif]
def EqFalse (x₀ : Prop) : Prop :=
  (¬x₀)

@[qualif]
def EqZero (x₀ : Int) : Prop :=
  (x₀ = 0)

@[qualif]
def GtZero (x₀ : Int) : Prop :=
  (x₀ > 0)

@[qualif]
def GeZero (x₀ : Int) : Prop :=
  (x₀ ≥ 0)

@[qualif]
def LtZero (x₀ : Int) : Prop :=
  (x₀ < 0)

@[qualif]
def LeZero (x₀ : Int) : Prop :=
  (x₀ ≤ 0)

@[qualif]
def Eq (x₀ : Int) (v₀ : Int) : Prop :=
  (x₀ = v₀)

@[qualif]
def Gt (x₀ : Int) (v₀ : Int) : Prop :=
  (x₀ > v₀)

@[qualif]
def Ge (x₀ : Int) (v₀ : Int) : Prop :=
  (x₀ ≥ v₀)

@[qualif]
def Lt (x₀ : Int) (v₀ : Int) : Prop :=
  (x₀ < v₀)

@[qualif]
def Le (x₀ : Int) (v₀ : Int) : Prop :=
  (x₀ ≤ v₀)

@[qualif]
def Le1 (x₀ : Int) (v₀ : Int) : Prop :=
  (x₀ ≤ (v₀ - 1))

end TestCountU32Qualifs

open TestCountU32Qualifs

set_option maxHeartbeats 5000000
def TestCountU32_proof : TestCountU32 := by
  unfold TestCountU32
  try solve_fixpoint

end F
