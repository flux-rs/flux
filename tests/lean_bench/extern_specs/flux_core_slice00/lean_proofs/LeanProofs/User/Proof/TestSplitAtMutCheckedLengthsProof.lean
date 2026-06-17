import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestSplitAtMutCheckedLengths
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestSplitAtMutCheckedLengthsQualifs

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

end TestSplitAtMutCheckedLengthsQualifs

open TestSplitAtMutCheckedLengthsQualifs

set_option maxHeartbeats 5000000
#time def TestSplitAtMutCheckedLengths_proof : TestSplitAtMutCheckedLengths := by
  unfold TestSplitAtMutCheckedLengths
  solve_fixpoint_combo

end F
