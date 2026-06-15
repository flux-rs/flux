import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Slice
open Classical
set_option linter.unusedVariables false


namespace F

namespace SliceQualifs

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
def Eq (a'₀ : Int) (v₀ : Int) : Prop :=
  (a'₀ = v₀)

@[qualif]
def Gt (a'₀ : Int) (v₀ : Int) : Prop :=
  (a'₀ > v₀)

@[qualif]
def Ge (a'₀ : Int) (v₀ : Int) : Prop :=
  (a'₀ ≥ v₀)

@[qualif]
def Lt (a'₀ : Int) (v₀ : Int) : Prop :=
  (a'₀ < v₀)

@[qualif]
def Le (a'₀ : Int) (v₀ : Int) : Prop :=
  (a'₀ ≤ v₀)

@[qualif]
def Le1 (a'₀ : Int) (v₀ : Int) : Prop :=
  (a'₀ ≤ (v₀ - 1))

end SliceQualifs

open SliceQualifs

set_option maxHeartbeats 5000000
def Slice_proof : Slice := by
  unfold Slice
  solve_fixpoint_combo

end F
