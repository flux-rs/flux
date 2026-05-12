import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FillVecLoop
open Classical

namespace F

namespace FillVecLoopQualifs

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
def Eq (f₀ : Int) (res₀ : Int) : Prop :=
  (f₀ = res₀)

@[qualif]
def Gt (f₀ : Int) (res₀ : Int) : Prop :=
  (f₀ > res₀)

@[qualif]
def Ge (f₀ : Int) (res₀ : Int) : Prop :=
  (f₀ ≥ res₀)

@[qualif]
def Lt (f₀ : Int) (res₀ : Int) : Prop :=
  (f₀ < res₀)

@[qualif]
def Le (f₀ : Int) (res₀ : Int) : Prop :=
  (f₀ ≤ res₀)

@[qualif]
def Le1 (f₀ : Int) (res₀ : Int) : Prop :=
  (f₀ ≤ (res₀ - 1))

end FillVecLoopQualifs

open FillVecLoopQualifs

def FillVecLoop_proof : FillVecLoop := by
  unfold FillVecLoop
  try solve_fixpoint

end F
