import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FftTest
open Classical
set_option linter.unusedVariables false


namespace F

namespace FftTestQualifs

@[qualif]
def EqTrue (v₀ : Prop) : Prop :=
  v₀

@[qualif]
def EqFalse (v₀ : Prop) : Prop :=
  (¬v₀)

@[qualif]
def EqZero (v₀ : Int) : Prop :=
  (v₀ = 0)

@[qualif]
def GtZero (v₀ : Int) : Prop :=
  (v₀ > 0)

@[qualif]
def GeZero (v₀ : Int) : Prop :=
  (v₀ ≥ 0)

@[qualif]
def LtZero (v₀ : Int) : Prop :=
  (v₀ < 0)

@[qualif]
def LeZero (v₀ : Int) : Prop :=
  (v₀ ≤ 0)

@[qualif]
def Eq (v₀ : Int) (i₀ : Int) : Prop :=
  (v₀ = i₀)

@[qualif]
def Gt (v₀ : Int) (i₀ : Int) : Prop :=
  (v₀ > i₀)

@[qualif]
def Ge (v₀ : Int) (i₀ : Int) : Prop :=
  (v₀ ≥ i₀)

@[qualif]
def Lt (v₀ : Int) (i₀ : Int) : Prop :=
  (v₀ < i₀)

@[qualif]
def Le (v₀ : Int) (i₀ : Int) : Prop :=
  (v₀ ≤ i₀)

@[qualif]
def Le1 (v₀ : Int) (i₀ : Int) : Prop :=
  (v₀ ≤ (i₀ - 1))

end FftTestQualifs

open FftTestQualifs

set_option maxHeartbeats 5000000
def FftTest_proof : FftTest := by
  unfold FftTest
  try solve_fixpoint

end F
