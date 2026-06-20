import LeanFixpoint
import Detached.DetachEnum01.Flux.Prelude
import Detached.DetachEnum01.Flux.VC.Cons
open Classical
set_option linter.unusedVariables false


namespace F

namespace ConsQualifs

@[qualif]
def EqTrue (h₀ : Prop) : Prop :=
  h₀

@[qualif]
def EqFalse (h₀ : Prop) : Prop :=
  (¬h₀)

@[qualif]
def EqZero (h₀ : Int) : Prop :=
  (h₀ = 0)

@[qualif]
def GtZero (h₀ : Int) : Prop :=
  (h₀ > 0)

@[qualif]
def GeZero (h₀ : Int) : Prop :=
  (h₀ ≥ 0)

@[qualif]
def LtZero (h₀ : Int) : Prop :=
  (h₀ < 0)

@[qualif]
def LeZero (h₀ : Int) : Prop :=
  (h₀ ≤ 0)

@[qualif]
def Eq (h₀ : Int) (a'₁ : Int) : Prop :=
  (h₀ = a'₁)

@[qualif]
def Gt (h₀ : Int) (a'₁ : Int) : Prop :=
  (h₀ > a'₁)

@[qualif]
def Ge (h₀ : Int) (a'₁ : Int) : Prop :=
  (h₀ ≥ a'₁)

@[qualif]
def Lt (h₀ : Int) (a'₁ : Int) : Prop :=
  (h₀ < a'₁)

@[qualif]
def Le (h₀ : Int) (a'₁ : Int) : Prop :=
  (h₀ ≤ a'₁)

@[qualif]
def Le1 (h₀ : Int) (a'₁ : Int) : Prop :=
  (h₀ ≤ (a'₁ - 1))

end ConsQualifs

open ConsQualifs

set_option maxHeartbeats 5000000
#time def Cons_proof : Cons := by
  unfold Cons
  solve_fixpoint_combo

end F
