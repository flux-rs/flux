import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__0__New
open Classical

namespace F

namespace Impl0NewQualifs

@[qualif]
def EqTrue (inner₀ : Prop) : Prop :=
  inner₀

@[qualif]
def EqFalse (inner₀ : Prop) : Prop :=
  (¬inner₀)

@[qualif]
def EqZero (inner₀ : Int) : Prop :=
  (inner₀ = 0)

@[qualif]
def GtZero (inner₀ : Int) : Prop :=
  (inner₀ > 0)

@[qualif]
def GeZero (inner₀ : Int) : Prop :=
  (inner₀ ≥ 0)

@[qualif]
def LtZero (inner₀ : Int) : Prop :=
  (inner₀ < 0)

@[qualif]
def LeZero (inner₀ : Int) : Prop :=
  (inner₀ ≤ 0)

@[qualif]
def Eq (inner₀ : Int) (i₀ : Int) : Prop :=
  (inner₀ = i₀)

@[qualif]
def Gt (inner₀ : Int) (i₀ : Int) : Prop :=
  (inner₀ > i₀)

@[qualif]
def Ge (inner₀ : Int) (i₀ : Int) : Prop :=
  (inner₀ ≥ i₀)

@[qualif]
def Lt (inner₀ : Int) (i₀ : Int) : Prop :=
  (inner₀ < i₀)

@[qualif]
def Le (inner₀ : Int) (i₀ : Int) : Prop :=
  (inner₀ ≤ i₀)

@[qualif]
def Le1 (inner₀ : Int) (i₀ : Int) : Prop :=
  (inner₀ ≤ (i₀ - 1))

end Impl0NewQualifs

open Impl0NewQualifs

set_option maxHeartbeats 5000000
def Impl__0__New_proof : Impl__0__New := by
  unfold Impl__0__New
  try solve_fixpoint

end F
