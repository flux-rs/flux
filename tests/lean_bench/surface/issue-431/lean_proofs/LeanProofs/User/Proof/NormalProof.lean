import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Normal
open Classical
set_option linter.unusedVariables false


namespace F

namespace NormalQualifs

@[qualif]
def EqTrue (w₀ : Prop) : Prop :=
  w₀

@[qualif]
def EqFalse (w₀ : Prop) : Prop :=
  (¬w₀)

@[qualif]
def EqZero (w₀ : Int) : Prop :=
  (w₀ = 0)

@[qualif]
def GtZero (w₀ : Int) : Prop :=
  (w₀ > 0)

@[qualif]
def GeZero (w₀ : Int) : Prop :=
  (w₀ ≥ 0)

@[qualif]
def LtZero (w₀ : Int) : Prop :=
  (w₀ < 0)

@[qualif]
def LeZero (w₀ : Int) : Prop :=
  (w₀ ≤ 0)

@[qualif]
def Eq (w₀ : Int) (i₀ : Int) : Prop :=
  (w₀ = i₀)

@[qualif]
def Gt (w₀ : Int) (i₀ : Int) : Prop :=
  (w₀ > i₀)

@[qualif]
def Ge (w₀ : Int) (i₀ : Int) : Prop :=
  (w₀ ≥ i₀)

@[qualif]
def Lt (w₀ : Int) (i₀ : Int) : Prop :=
  (w₀ < i₀)

@[qualif]
def Le (w₀ : Int) (i₀ : Int) : Prop :=
  (w₀ ≤ i₀)

@[qualif]
def Le1 (w₀ : Int) (i₀ : Int) : Prop :=
  (w₀ ≤ (i₀ - 1))

end NormalQualifs

open NormalQualifs

set_option maxHeartbeats 5000000
def Normal_proof : Normal := by
  unfold Normal
  solve_fixpoint_combo

end F
