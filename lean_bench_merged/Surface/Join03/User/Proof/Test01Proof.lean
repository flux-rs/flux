import LeanFixpoint
import Surface.Join03.Flux.Prelude
import Surface.Join03.Flux.VC.Test01
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test01Qualifs

@[qualif]
def EqTrue (p₁ : Prop) : Prop :=
  p₁

@[qualif]
def EqFalse (p₁ : Prop) : Prop :=
  (¬p₁)

@[qualif]
def EqZero (p₁ : Int) : Prop :=
  (p₁ = 0)

@[qualif]
def GtZero (p₁ : Int) : Prop :=
  (p₁ > 0)

@[qualif]
def GeZero (p₁ : Int) : Prop :=
  (p₁ ≥ 0)

@[qualif]
def LtZero (p₁ : Int) : Prop :=
  (p₁ < 0)

@[qualif]
def LeZero (p₁ : Int) : Prop :=
  (p₁ ≤ 0)

@[qualif]
def Eq (p₁ : Int) (i₀ : Int) : Prop :=
  (p₁ = i₀)

@[qualif]
def Gt (p₁ : Int) (i₀ : Int) : Prop :=
  (p₁ > i₀)

@[qualif]
def Ge (p₁ : Int) (i₀ : Int) : Prop :=
  (p₁ ≥ i₀)

@[qualif]
def Lt (p₁ : Int) (i₀ : Int) : Prop :=
  (p₁ < i₀)

@[qualif]
def Le (p₁ : Int) (i₀ : Int) : Prop :=
  (p₁ ≤ i₀)

@[qualif]
def Le1 (p₁ : Int) (i₀ : Int) : Prop :=
  (p₁ ≤ (i₀ - 1))

end Test01Qualifs

open Test01Qualifs

set_option maxHeartbeats 5000000
#time def Test01_proof : Test01 := by
  unfold Test01
  solve_fixpoint_combo

end F
