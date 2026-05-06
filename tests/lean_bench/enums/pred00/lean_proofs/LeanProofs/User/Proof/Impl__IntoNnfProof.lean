import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__IntoNnf
open Classical

namespace F

namespace ImplIntoNnfQualifs

@[qualif]
def EqTrue (self₀ : Prop) : Prop :=
  self₀

@[qualif]
def EqFalse (self₀ : Prop) : Prop :=
  (¬self₀)

@[qualif]
def EqZero (self₀ : Int) : Prop :=
  (self₀ = 0)

@[qualif]
def GtZero (self₀ : Int) : Prop :=
  (self₀ > 0)

@[qualif]
def GeZero (self₀ : Int) : Prop :=
  (self₀ ≥ 0)

@[qualif]
def LtZero (self₀ : Int) : Prop :=
  (self₀ < 0)

@[qualif]
def LeZero (self₀ : Int) : Prop :=
  (self₀ ≤ 0)

@[qualif]
def Eq (self₀ : Int) (a'₁ : Int) : Prop :=
  (self₀ = a'₁)

@[qualif]
def Gt (self₀ : Int) (a'₁ : Int) : Prop :=
  (self₀ > a'₁)

@[qualif]
def Ge (self₀ : Int) (a'₁ : Int) : Prop :=
  (self₀ ≥ a'₁)

@[qualif]
def Lt (self₀ : Int) (a'₁ : Int) : Prop :=
  (self₀ < a'₁)

@[qualif]
def Le (self₀ : Int) (a'₁ : Int) : Prop :=
  (self₀ ≤ a'₁)

@[qualif]
def Le1 (self₀ : Int) (a'₁ : Int) : Prop :=
  (self₀ ≤ (a'₁ - 1))

end ImplIntoNnfQualifs

open ImplIntoNnfQualifs

set_option maxHeartbeats 1500000

def Impl__IntoNnf_proof : Impl__IntoNnf := by
  unfold Impl__IntoNnf
  try solve_fixpoint
end F
