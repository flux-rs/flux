import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestSplitAtCheckedOutOfBounds
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestSplitAtCheckedOutOfBoundsQualifs

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
def Eq (a'₀ : Int) (mid₀ : Int) : Prop :=
  (a'₀ = mid₀)

@[qualif]
def Gt (a'₀ : Int) (mid₀ : Int) : Prop :=
  (a'₀ > mid₀)

@[qualif]
def Ge (a'₀ : Int) (mid₀ : Int) : Prop :=
  (a'₀ ≥ mid₀)

@[qualif]
def Lt (a'₀ : Int) (mid₀ : Int) : Prop :=
  (a'₀ < mid₀)

@[qualif]
def Le (a'₀ : Int) (mid₀ : Int) : Prop :=
  (a'₀ ≤ mid₀)

@[qualif]
def Le1 (a'₀ : Int) (mid₀ : Int) : Prop :=
  (a'₀ ≤ (mid₀ - 1))

end TestSplitAtCheckedOutOfBoundsQualifs

open TestSplitAtCheckedOutOfBoundsQualifs

set_option maxHeartbeats 5000000
def TestSplitAtCheckedOutOfBounds_proof : TestSplitAtCheckedOutOfBounds := by
  unfold TestSplitAtCheckedOutOfBounds
  try solve_fixpoint

end F
