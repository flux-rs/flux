import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Foo3
open Classical
set_option linter.unusedVariables false


namespace F

namespace Foo3Qualifs

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
def Eq (f₀ : Int) (a'₁ : Int) : Prop :=
  (f₀ = a'₁)

@[qualif]
def Gt (f₀ : Int) (a'₁ : Int) : Prop :=
  (f₀ > a'₁)

@[qualif]
def Ge (f₀ : Int) (a'₁ : Int) : Prop :=
  (f₀ ≥ a'₁)

@[qualif]
def Lt (f₀ : Int) (a'₁ : Int) : Prop :=
  (f₀ < a'₁)

@[qualif]
def Le (f₀ : Int) (a'₁ : Int) : Prop :=
  (f₀ ≤ a'₁)

@[qualif]
def Le1 (f₀ : Int) (a'₁ : Int) : Prop :=
  (f₀ ≤ (a'₁ - 1))

end Foo3Qualifs

open Foo3Qualifs

set_option maxHeartbeats 5000000
def Foo3_proof : Foo3 := by
  unfold Foo3
  solve_fixpoint_combo

end F
