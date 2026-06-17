import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test00
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test00Qualifs

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

end Test00Qualifs

open Test00Qualifs

set_option maxHeartbeats 5000000
#time def Test00_proof : Test00 := by
  unfold Test00
  solve_fixpoint_combo

end F
