import LeanFixpoint
import Surface.Loop00.Flux.Prelude
import Surface.Loop00.Flux.VC.Test
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestQualifs

@[qualif]
def EqTrue (k₁ : Prop) : Prop :=
  k₁

@[qualif]
def EqFalse (k₁ : Prop) : Prop :=
  (¬k₁)

@[qualif]
def EqZero (k₁ : Int) : Prop :=
  (k₁ = 0)

@[qualif]
def GtZero (k₁ : Int) : Prop :=
  (k₁ > 0)

@[qualif]
def GeZero (k₁ : Int) : Prop :=
  (k₁ ≥ 0)

@[qualif]
def LtZero (k₁ : Int) : Prop :=
  (k₁ < 0)

@[qualif]
def LeZero (k₁ : Int) : Prop :=
  (k₁ ≤ 0)

@[qualif]
def Eq (k₁ : Int) (a'₁ : Int) : Prop :=
  (k₁ = a'₁)

@[qualif]
def Gt (k₁ : Int) (a'₁ : Int) : Prop :=
  (k₁ > a'₁)

@[qualif]
def Ge (k₁ : Int) (a'₁ : Int) : Prop :=
  (k₁ ≥ a'₁)

@[qualif]
def Lt (k₁ : Int) (a'₁ : Int) : Prop :=
  (k₁ < a'₁)

@[qualif]
def Le (k₁ : Int) (a'₁ : Int) : Prop :=
  (k₁ ≤ a'₁)

@[qualif]
def Le1 (k₁ : Int) (a'₁ : Int) : Prop :=
  (k₁ ≤ (a'₁ - 1))

end TestQualifs

open TestQualifs

set_option maxHeartbeats 5000000
#time def Test_proof : Test := by
  unfold Test
  solve_fixpoint_combo

end F
