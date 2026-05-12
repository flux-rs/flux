import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__1__Push
open Classical

namespace F

namespace Impl1PushQualifs

@[qualif]
def EqTrue (elem₀ : Prop) : Prop :=
  elem₀

@[qualif]
def EqFalse (elem₀ : Prop) : Prop :=
  (¬elem₀)

@[qualif]
def EqZero (elem₀ : Int) : Prop :=
  (elem₀ = 0)

@[qualif]
def GtZero (elem₀ : Int) : Prop :=
  (elem₀ > 0)

@[qualif]
def GeZero (elem₀ : Int) : Prop :=
  (elem₀ ≥ 0)

@[qualif]
def LtZero (elem₀ : Int) : Prop :=
  (elem₀ < 0)

@[qualif]
def LeZero (elem₀ : Int) : Prop :=
  (elem₀ ≤ 0)

@[qualif]
def Eq (elem₀ : Int) (a'₁ : Int) : Prop :=
  (elem₀ = a'₁)

@[qualif]
def Gt (elem₀ : Int) (a'₁ : Int) : Prop :=
  (elem₀ > a'₁)

@[qualif]
def Ge (elem₀ : Int) (a'₁ : Int) : Prop :=
  (elem₀ ≥ a'₁)

@[qualif]
def Lt (elem₀ : Int) (a'₁ : Int) : Prop :=
  (elem₀ < a'₁)

@[qualif]
def Le (elem₀ : Int) (a'₁ : Int) : Prop :=
  (elem₀ ≤ a'₁)

@[qualif]
def Le1 (elem₀ : Int) (a'₁ : Int) : Prop :=
  (elem₀ ≤ (a'₁ - 1))

end Impl1PushQualifs

open Impl1PushQualifs

def Impl__1__Push_proof : Impl__1__Push := by
  unfold Impl__1__Push
  try solve_fixpoint

end F
