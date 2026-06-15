import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestSplitFirstTailLen
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestSplitFirstTailLenQualifs

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
def Eq (a'₀ : Int) (xs_elem₀ : Int) : Prop :=
  (a'₀ = xs_elem₀)

@[qualif]
def Gt (a'₀ : Int) (xs_elem₀ : Int) : Prop :=
  (a'₀ > xs_elem₀)

@[qualif]
def Ge (a'₀ : Int) (xs_elem₀ : Int) : Prop :=
  (a'₀ ≥ xs_elem₀)

@[qualif]
def Lt (a'₀ : Int) (xs_elem₀ : Int) : Prop :=
  (a'₀ < xs_elem₀)

@[qualif]
def Le (a'₀ : Int) (xs_elem₀ : Int) : Prop :=
  (a'₀ ≤ xs_elem₀)

@[qualif]
def Le1 (a'₀ : Int) (xs_elem₀ : Int) : Prop :=
  (a'₀ ≤ (xs_elem₀ - 1))

end TestSplitFirstTailLenQualifs

open TestSplitFirstTailLenQualifs

set_option maxHeartbeats 5000000
def TestSplitFirstTailLen_proof : TestSplitFirstTailLen := by
  unfold TestSplitFirstTailLen
  solve_fixpoint_combo

end F
