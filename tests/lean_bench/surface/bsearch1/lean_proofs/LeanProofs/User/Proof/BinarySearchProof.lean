import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.BinarySearch
open Classical
set_option linter.unusedVariables false


namespace F

namespace BinarySearchQualifs

@[qualif]
def EqTrue (k₀ : Prop) : Prop :=
  k₀

@[qualif]
def EqFalse (k₀ : Prop) : Prop :=
  (¬k₀)

@[qualif]
def EqZero (k₀ : Int) : Prop :=
  (k₀ = 0)

@[qualif]
def GtZero (k₀ : Int) : Prop :=
  (k₀ > 0)

@[qualif]
def GeZero (k₀ : Int) : Prop :=
  (k₀ ≥ 0)

@[qualif]
def LtZero (k₀ : Int) : Prop :=
  (k₀ < 0)

@[qualif]
def LeZero (k₀ : Int) : Prop :=
  (k₀ ≤ 0)

@[qualif]
def Eq (k₀ : Int) (low₀ : Int) : Prop :=
  (k₀ = low₀)

@[qualif]
def Gt (k₀ : Int) (low₀ : Int) : Prop :=
  (k₀ > low₀)

@[qualif]
def Ge (k₀ : Int) (low₀ : Int) : Prop :=
  (k₀ ≥ low₀)

@[qualif]
def Lt (k₀ : Int) (low₀ : Int) : Prop :=
  (k₀ < low₀)

@[qualif]
def Le (k₀ : Int) (low₀ : Int) : Prop :=
  (k₀ ≤ low₀)

@[qualif]
def Le1 (k₀ : Int) (low₀ : Int) : Prop :=
  (k₀ ≤ (low₀ - 1))

end BinarySearchQualifs

open BinarySearchQualifs

set_option maxHeartbeats 5000000
#time def BinarySearch_proof : BinarySearch := by
  unfold BinarySearch
  solve_fixpoint_combo

end F
