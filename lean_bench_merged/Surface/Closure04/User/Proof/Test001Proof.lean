import LeanFixpoint
import Surface.Closure04.Flux.Prelude
import Surface.Closure04.Flux.VC.Test001
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test001Qualifs

@[qualif]
def EqTrue (frog₀ : Prop) : Prop :=
  frog₀

@[qualif]
def EqFalse (frog₀ : Prop) : Prop :=
  (¬frog₀)

@[qualif]
def EqZero (frog₀ : Int) : Prop :=
  (frog₀ = 0)

@[qualif]
def GtZero (frog₀ : Int) : Prop :=
  (frog₀ > 0)

@[qualif]
def GeZero (frog₀ : Int) : Prop :=
  (frog₀ ≥ 0)

@[qualif]
def LtZero (frog₀ : Int) : Prop :=
  (frog₀ < 0)

@[qualif]
def LeZero (frog₀ : Int) : Prop :=
  (frog₀ ≤ 0)

@[qualif]
def Eq (frog₀ : Int) (a'₁ : Int) : Prop :=
  (frog₀ = a'₁)

@[qualif]
def Gt (frog₀ : Int) (a'₁ : Int) : Prop :=
  (frog₀ > a'₁)

@[qualif]
def Ge (frog₀ : Int) (a'₁ : Int) : Prop :=
  (frog₀ ≥ a'₁)

@[qualif]
def Lt (frog₀ : Int) (a'₁ : Int) : Prop :=
  (frog₀ < a'₁)

@[qualif]
def Le (frog₀ : Int) (a'₁ : Int) : Prop :=
  (frog₀ ≤ a'₁)

@[qualif]
def Le1 (frog₀ : Int) (a'₁ : Int) : Prop :=
  (frog₀ ≤ (a'₁ - 1))

end Test001Qualifs

open Test001Qualifs

set_option maxHeartbeats 5000000
#time def Test001_proof : Test001 := by
  unfold Test001
  solve_fixpoint_combo

end F
