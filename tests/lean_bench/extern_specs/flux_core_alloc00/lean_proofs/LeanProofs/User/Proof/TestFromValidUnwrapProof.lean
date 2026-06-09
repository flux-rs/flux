import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestFromValidUnwrap
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestFromValidUnwrapQualifs

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
def Eq (a'₀ : Int) (x₀ : Int) : Prop :=
  (a'₀ = x₀)

@[qualif]
def Gt (a'₀ : Int) (x₀ : Int) : Prop :=
  (a'₀ > x₀)

@[qualif]
def Ge (a'₀ : Int) (x₀ : Int) : Prop :=
  (a'₀ ≥ x₀)

@[qualif]
def Lt (a'₀ : Int) (x₀ : Int) : Prop :=
  (a'₀ < x₀)

@[qualif]
def Le (a'₀ : Int) (x₀ : Int) : Prop :=
  (a'₀ ≤ x₀)

@[qualif]
def Le1 (a'₀ : Int) (x₀ : Int) : Prop :=
  (a'₀ ≤ (x₀ - 1))

end TestFromValidUnwrapQualifs

open TestFromValidUnwrapQualifs

set_option maxHeartbeats 5000000
def TestFromValidUnwrap_proof : TestFromValidUnwrap := by
  unfold TestFromValidUnwrap
  try solve_fixpoint

end F
