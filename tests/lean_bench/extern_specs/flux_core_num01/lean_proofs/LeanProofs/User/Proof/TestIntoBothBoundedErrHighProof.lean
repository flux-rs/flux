import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestIntoBothBoundedErrHigh
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestIntoBothBoundedErrHighQualifs

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
def Eq (x₀ : Int) (r₀ : Int) : Prop :=
  (x₀ = r₀)

@[qualif]
def Gt (x₀ : Int) (r₀ : Int) : Prop :=
  (x₀ > r₀)

@[qualif]
def Ge (x₀ : Int) (r₀ : Int) : Prop :=
  (x₀ ≥ r₀)

@[qualif]
def Lt (x₀ : Int) (r₀ : Int) : Prop :=
  (x₀ < r₀)

@[qualif]
def Le (x₀ : Int) (r₀ : Int) : Prop :=
  (x₀ ≤ r₀)

@[qualif]
def Le1 (x₀ : Int) (r₀ : Int) : Prop :=
  (x₀ ≤ (r₀ - 1))

end TestIntoBothBoundedErrHighQualifs

open TestIntoBothBoundedErrHighQualifs

set_option maxHeartbeats 5000000
#time def TestIntoBothBoundedErrHigh_proof : TestIntoBothBoundedErrHigh := by
  unfold TestIntoBothBoundedErrHigh
  solve_fixpoint_combo

end F
