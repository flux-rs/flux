import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CastToU8AndBack
open Classical

namespace F

namespace CastToU8AndBackQualifs

@[qualif]
def EqTrue (a'₀ : Prop) : Prop :=
  a'₀

@[qualif]
def EqFalse (a'₀ : Prop) : Prop :=
  (¬a'₀)

@[qualif]
def EqZero (a'₀ : Int) : Prop :=
  (a'₀ = 0)

@[qualif]
def GtZero (a'₀ : Int) : Prop :=
  (a'₀ > 0)

@[qualif]
def GeZero (a'₀ : Int) : Prop :=
  (a'₀ ≥ 0)

@[qualif]
def LtZero (a'₀ : Int) : Prop :=
  (a'₀ < 0)

@[qualif]
def LeZero (a'₀ : Int) : Prop :=
  (a'₀ ≤ 0)

@[qualif]
def Eq (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ = a'₁)

@[qualif]
def Gt (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ > a'₁)

@[qualif]
def Ge (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ ≥ a'₁)

@[qualif]
def Lt (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ < a'₁)

@[qualif]
def Le (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ ≤ a'₁)

@[qualif]
def Le1 (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ ≤ (a'₁ - 1))

end CastToU8AndBackQualifs

open CastToU8AndBackQualifs

def CastToU8AndBack_proof : CastToU8AndBack := by
  unfold CastToU8AndBack
  try solve_fixpoint

end F
