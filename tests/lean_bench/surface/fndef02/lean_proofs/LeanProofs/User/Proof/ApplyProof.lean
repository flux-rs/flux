import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Apply
open Classical

namespace F

namespace ApplyQualifs

@[qualif]
def EqTrue (f₀ : Prop) : Prop :=
  f₀

@[qualif]
def EqFalse (f₀ : Prop) : Prop :=
  (¬f₀)

@[qualif]
def EqZero (f₀ : Int) : Prop :=
  (f₀ = 0)

@[qualif]
def GtZero (f₀ : Int) : Prop :=
  (f₀ > 0)

@[qualif]
def GeZero (f₀ : Int) : Prop :=
  (f₀ ≥ 0)

@[qualif]
def LtZero (f₀ : Int) : Prop :=
  (f₀ < 0)

@[qualif]
def LeZero (f₀ : Int) : Prop :=
  (f₀ ≤ 0)

@[qualif]
def Eq (f₀ : Int) (x₀ : Int) : Prop :=
  (f₀ = x₀)

@[qualif]
def Gt (f₀ : Int) (x₀ : Int) : Prop :=
  (f₀ > x₀)

@[qualif]
def Ge (f₀ : Int) (x₀ : Int) : Prop :=
  (f₀ ≥ x₀)

@[qualif]
def Lt (f₀ : Int) (x₀ : Int) : Prop :=
  (f₀ < x₀)

@[qualif]
def Le (f₀ : Int) (x₀ : Int) : Prop :=
  (f₀ ≤ x₀)

@[qualif]
def Le1 (f₀ : Int) (x₀ : Int) : Prop :=
  (f₀ ≤ (x₀ - 1))

end ApplyQualifs

open ApplyQualifs

def Apply_proof : Apply := by
  unfold Apply
  try solve_fixpoint

end F
