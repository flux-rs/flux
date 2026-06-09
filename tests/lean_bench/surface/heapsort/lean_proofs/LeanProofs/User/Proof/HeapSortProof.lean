import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.HeapSort
open Classical
set_option linter.unusedVariables false


namespace F

namespace HeapSortQualifs

@[qualif]
def EqTrue (start₀ : Prop) : Prop :=
  start₀

@[qualif]
def EqFalse (start₀ : Prop) : Prop :=
  (¬start₀)

@[qualif]
def EqZero (start₀ : Int) : Prop :=
  (start₀ = 0)

@[qualif]
def GtZero (start₀ : Int) : Prop :=
  (start₀ > 0)

@[qualif]
def GeZero (start₀ : Int) : Prop :=
  (start₀ ≥ 0)

@[qualif]
def LtZero (start₀ : Int) : Prop :=
  (start₀ < 0)

@[qualif]
def LeZero (start₀ : Int) : Prop :=
  (start₀ ≤ 0)

@[qualif]
def Eq (start₀ : Int) (end₀ : Int) : Prop :=
  (start₀ = end₀)

@[qualif]
def Gt (start₀ : Int) (end₀ : Int) : Prop :=
  (start₀ > end₀)

@[qualif]
def Ge (start₀ : Int) (end₀ : Int) : Prop :=
  (start₀ ≥ end₀)

@[qualif]
def Lt (start₀ : Int) (end₀ : Int) : Prop :=
  (start₀ < end₀)

@[qualif]
def Le (start₀ : Int) (end₀ : Int) : Prop :=
  (start₀ ≤ end₀)

@[qualif]
def Le1 (start₀ : Int) (end₀ : Int) : Prop :=
  (start₀ ≤ (end₀ - 1))

end HeapSortQualifs

open HeapSortQualifs

set_option maxHeartbeats 5000000
def HeapSort_proof : HeapSort := by
  unfold HeapSort
  try solve_fixpoint

end F
