import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.UpdateCenters
open Classical
set_option linter.unusedVariables false


namespace F

namespace UpdateCentersQualifs

@[qualif]
def EqTrue (new_centers₀ : Prop) : Prop :=
  new_centers₀

@[qualif]
def EqFalse (new_centers₀ : Prop) : Prop :=
  (¬new_centers₀)

@[qualif]
def EqZero (new_centers₀ : Int) : Prop :=
  (new_centers₀ = 0)

@[qualif]
def GtZero (new_centers₀ : Int) : Prop :=
  (new_centers₀ > 0)

@[qualif]
def GeZero (new_centers₀ : Int) : Prop :=
  (new_centers₀ ≥ 0)

@[qualif]
def LtZero (new_centers₀ : Int) : Prop :=
  (new_centers₀ < 0)

@[qualif]
def LeZero (new_centers₀ : Int) : Prop :=
  (new_centers₀ ≤ 0)

@[qualif]
def Eq (new_centers₀ : Int) (v₀ : Int) : Prop :=
  (new_centers₀ = v₀)

@[qualif]
def Gt (new_centers₀ : Int) (v₀ : Int) : Prop :=
  (new_centers₀ > v₀)

@[qualif]
def Ge (new_centers₀ : Int) (v₀ : Int) : Prop :=
  (new_centers₀ ≥ v₀)

@[qualif]
def Lt (new_centers₀ : Int) (v₀ : Int) : Prop :=
  (new_centers₀ < v₀)

@[qualif]
def Le (new_centers₀ : Int) (v₀ : Int) : Prop :=
  (new_centers₀ ≤ v₀)

@[qualif]
def Le1 (new_centers₀ : Int) (v₀ : Int) : Prop :=
  (new_centers₀ ≤ (v₀ - 1))

end UpdateCentersQualifs

open UpdateCentersQualifs

set_option maxHeartbeats 5000000
def UpdateCenters_proof : UpdateCenters := by
  unfold UpdateCenters
  try solve_fixpoint

end F
