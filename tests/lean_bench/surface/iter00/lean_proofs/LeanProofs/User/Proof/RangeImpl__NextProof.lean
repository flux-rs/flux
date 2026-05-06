import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RangeImpl__Next
open Classical

namespace F

namespace RangeImplNextQualifs

@[qualif]
def EqTrue (v₀ : Prop) : Prop :=
  v₀

@[qualif]
def EqFalse (v₀ : Prop) : Prop :=
  (¬v₀)

@[qualif]
def EqZero (v₀ : Int) : Prop :=
  (v₀ = 0)

@[qualif]
def GtZero (v₀ : Int) : Prop :=
  (v₀ > 0)

@[qualif]
def GeZero (v₀ : Int) : Prop :=
  (v₀ ≥ 0)

@[qualif]
def LtZero (v₀ : Int) : Prop :=
  (v₀ < 0)

@[qualif]
def LeZero (v₀ : Int) : Prop :=
  (v₀ ≤ 0)

@[qualif]
def Eq (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ = a'₁)

@[qualif]
def Gt (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ > a'₁)

@[qualif]
def Ge (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ ≥ a'₁)

@[qualif]
def Lt (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ < a'₁)

@[qualif]
def Le (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ ≤ a'₁)

@[qualif]
def Le1 (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ ≤ (a'₁ - 1))

end RangeImplNextQualifs

open RangeImplNextQualifs

def RangeImpl__Next_proof : RangeImpl__Next := by
  unfold RangeImpl__Next
  try solve_fixpoint

end F
