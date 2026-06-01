import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Doit
open Classical

namespace F

namespace DoitQualifs

@[qualif]
def EqTrue (np₀ : Prop) : Prop :=
  np₀

@[qualif]
def EqFalse (np₀ : Prop) : Prop :=
  (¬np₀)

@[qualif]
def EqZero (np₀ : Int) : Prop :=
  (np₀ = 0)

@[qualif]
def GtZero (np₀ : Int) : Prop :=
  (np₀ > 0)

@[qualif]
def GeZero (np₀ : Int) : Prop :=
  (np₀ ≥ 0)

@[qualif]
def LtZero (np₀ : Int) : Prop :=
  (np₀ < 0)

@[qualif]
def LeZero (np₀ : Int) : Prop :=
  (np₀ ≤ 0)

@[qualif]
def Eq (np₀ : Int) (i₀ : Int) : Prop :=
  (np₀ = i₀)

@[qualif]
def Gt (np₀ : Int) (i₀ : Int) : Prop :=
  (np₀ > i₀)

@[qualif]
def Ge (np₀ : Int) (i₀ : Int) : Prop :=
  (np₀ ≥ i₀)

@[qualif]
def Lt (np₀ : Int) (i₀ : Int) : Prop :=
  (np₀ < i₀)

@[qualif]
def Le (np₀ : Int) (i₀ : Int) : Prop :=
  (np₀ ≤ i₀)

@[qualif]
def Le1 (np₀ : Int) (i₀ : Int) : Prop :=
  (np₀ ≤ (i₀ - 1))

end DoitQualifs

open DoitQualifs

set_option maxHeartbeats 5000000
def Doit_proof : Doit := by
  unfold Doit
  try solve_fixpoint

end F
