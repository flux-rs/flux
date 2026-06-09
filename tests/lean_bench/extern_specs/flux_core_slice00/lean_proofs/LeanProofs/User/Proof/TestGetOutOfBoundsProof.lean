import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestGetOutOfBounds
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestGetOutOfBoundsQualifs

@[qualif]
def EqTrue (a'₀ : Prop) : Prop :=
  a'₀

@[qualif]
def EqFalse (a'₀ : Prop) : Prop :=
  (¬a'₀)

@[qualif]
def EqZero (a'₀ : Int) : Prop :=
  (a'₀ = 0)

@[qualif]
def GtZero (a'₀ : Int) : Prop :=
  (a'₀ > 0)

@[qualif]
def GeZero (a'₀ : Int) : Prop :=
  (a'₀ ≥ 0)

@[qualif]
def LtZero (a'₀ : Int) : Prop :=
  (a'₀ < 0)

@[qualif]
def LeZero (a'₀ : Int) : Prop :=
  (a'₀ ≤ 0)

@[qualif]
def Eq (a'₀ : Int) (i₀ : Int) : Prop :=
  (a'₀ = i₀)

@[qualif]
def Gt (a'₀ : Int) (i₀ : Int) : Prop :=
  (a'₀ > i₀)

@[qualif]
def Ge (a'₀ : Int) (i₀ : Int) : Prop :=
  (a'₀ ≥ i₀)

@[qualif]
def Lt (a'₀ : Int) (i₀ : Int) : Prop :=
  (a'₀ < i₀)

@[qualif]
def Le (a'₀ : Int) (i₀ : Int) : Prop :=
  (a'₀ ≤ i₀)

@[qualif]
def Le1 (a'₀ : Int) (i₀ : Int) : Prop :=
  (a'₀ ≤ (i₀ - 1))

end TestGetOutOfBoundsQualifs

open TestGetOutOfBoundsQualifs

set_option maxHeartbeats 5000000
def TestGetOutOfBounds_proof : TestGetOutOfBounds := by
  unfold TestGetOutOfBounds
  try solve_fixpoint

end F
