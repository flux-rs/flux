import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__1__Foreach
open Classical

namespace F

namespace Impl1ForeachQualifs

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
def Eq (f₀ : Int) (i₀ : Int) : Prop :=
  (f₀ = i₀)

@[qualif]
def Gt (f₀ : Int) (i₀ : Int) : Prop :=
  (f₀ > i₀)

@[qualif]
def Ge (f₀ : Int) (i₀ : Int) : Prop :=
  (f₀ ≥ i₀)

@[qualif]
def Lt (f₀ : Int) (i₀ : Int) : Prop :=
  (f₀ < i₀)

@[qualif]
def Le (f₀ : Int) (i₀ : Int) : Prop :=
  (f₀ ≤ i₀)

@[qualif]
def Le1 (f₀ : Int) (i₀ : Int) : Prop :=
  (f₀ ≤ (i₀ - 1))

end Impl1ForeachQualifs

open Impl1ForeachQualifs

def Impl__1__Foreach_proof : Impl__1__Foreach := by
  unfold Impl__1__Foreach
  try solve_fixpoint

end F
