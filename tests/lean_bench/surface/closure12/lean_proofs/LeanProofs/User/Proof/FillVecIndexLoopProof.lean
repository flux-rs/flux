import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FillVecIndexLoop
open Classical
set_option linter.unusedVariables false


namespace F

namespace FillVecIndexLoopQualifs

@[qualif]
def EqTrue (f₀ : Prop) : Prop :=
  f₀

@[qualif]
def EqFalse (f₀ : Prop) : Prop :=
  (¬f₀)

@[qualif]
def EqZero (f₀ : Int) : Prop :=
  (f₀ = 0)

@[qualif]
def GtZero (f₀ : Int) : Prop :=
  (f₀ > 0)

@[qualif]
def GeZero (f₀ : Int) : Prop :=
  (f₀ ≥ 0)

@[qualif]
def LtZero (f₀ : Int) : Prop :=
  (f₀ < 0)

@[qualif]
def LeZero (f₀ : Int) : Prop :=
  (f₀ ≤ 0)

@[qualif]
def Eq (f₀ : Int) (f₁ : Int) : Prop :=
  (f₀ = f₁)

@[qualif]
def Gt (f₀ : Int) (f₁ : Int) : Prop :=
  (f₀ > f₁)

@[qualif]
def Ge (f₀ : Int) (f₁ : Int) : Prop :=
  (f₀ ≥ f₁)

@[qualif]
def Lt (f₀ : Int) (f₁ : Int) : Prop :=
  (f₀ < f₁)

@[qualif]
def Le (f₀ : Int) (f₁ : Int) : Prop :=
  (f₀ ≤ f₁)

@[qualif]
def Le1 (f₀ : Int) (f₁ : Int) : Prop :=
  (f₀ ≤ (f₁ - 1))

end FillVecIndexLoopQualifs

open FillVecIndexLoopQualifs

set_option maxHeartbeats 5000000
set_option maxRecDepth 1024
def FillVecIndexLoop_proof : FillVecIndexLoop := by
  unfold FillVecIndexLoop
  try solve_fixpoint

end F
