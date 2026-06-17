import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestQualifs

@[qualif]
def Foo (a'₁ : Int) : Prop :=
  (foo a'₁)

@[qualif]
def EqTrue (i₀ : Prop) : Prop :=
  i₀

@[qualif]
def EqFalse (i₀ : Prop) : Prop :=
  (¬i₀)

@[qualif]
def EqZero (i₀ : Int) : Prop :=
  (i₀ = 0)

@[qualif]
def GtZero (i₀ : Int) : Prop :=
  (i₀ > 0)

@[qualif]
def GeZero (i₀ : Int) : Prop :=
  (i₀ ≥ 0)

@[qualif]
def LtZero (i₀ : Int) : Prop :=
  (i₀ < 0)

@[qualif]
def LeZero (i₀ : Int) : Prop :=
  (i₀ ≤ 0)

@[qualif]
def Eq (i₀ : Int) (a'₁ : Int) : Prop :=
  (i₀ = a'₁)

@[qualif]
def Gt (i₀ : Int) (a'₁ : Int) : Prop :=
  (i₀ > a'₁)

@[qualif]
def Ge (i₀ : Int) (a'₁ : Int) : Prop :=
  (i₀ ≥ a'₁)

@[qualif]
def Lt (i₀ : Int) (a'₁ : Int) : Prop :=
  (i₀ < a'₁)

@[qualif]
def Le (i₀ : Int) (a'₁ : Int) : Prop :=
  (i₀ ≤ a'₁)

@[qualif]
def Le1 (i₀ : Int) (a'₁ : Int) : Prop :=
  (i₀ ≤ (a'₁ - 1))

end TestQualifs

open TestQualifs

set_option maxHeartbeats 5000000
#time def Test_proof : Test := by
  unfold Test
  solve_fixpoint_combo

end F
