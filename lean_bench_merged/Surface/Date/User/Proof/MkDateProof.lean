import LeanFixpoint
import Surface.Date.Flux.Prelude
import Surface.Date.Flux.VC.MkDate
open Classical
set_option linter.unusedVariables false


namespace F

namespace MkDateQualifs

@[qualif]
def EqTrue (day₀ : Prop) : Prop :=
  day₀

@[qualif]
def EqFalse (day₀ : Prop) : Prop :=
  (¬day₀)

@[qualif]
def EqZero (day₀ : Int) : Prop :=
  (day₀ = 0)

@[qualif]
def GtZero (day₀ : Int) : Prop :=
  (day₀ > 0)

@[qualif]
def GeZero (day₀ : Int) : Prop :=
  (day₀ ≥ 0)

@[qualif]
def LtZero (day₀ : Int) : Prop :=
  (day₀ < 0)

@[qualif]
def LeZero (day₀ : Int) : Prop :=
  (day₀ ≤ 0)

@[qualif]
def Eq (day₀ : Int) (month₀ : Int) : Prop :=
  (day₀ = month₀)

@[qualif]
def Gt (day₀ : Int) (month₀ : Int) : Prop :=
  (day₀ > month₀)

@[qualif]
def Ge (day₀ : Int) (month₀ : Int) : Prop :=
  (day₀ ≥ month₀)

@[qualif]
def Lt (day₀ : Int) (month₀ : Int) : Prop :=
  (day₀ < month₀)

@[qualif]
def Le (day₀ : Int) (month₀ : Int) : Prop :=
  (day₀ ≤ month₀)

@[qualif]
def Le1 (day₀ : Int) (month₀ : Int) : Prop :=
  (day₀ ≤ (month₀ - 1))

end MkDateQualifs

open MkDateQualifs

set_option maxHeartbeats 5000000
#time def MkDate_proof : MkDate := by
  unfold MkDate
  solve_fixpoint_combo

end F
