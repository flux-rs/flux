import LeanFixpoint
import Surface.AssumeInvariant00.Flux.Prelude
import Surface.AssumeInvariant00.Flux.VC.Test01
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test01Qualifs

@[qualif]
def EqTrue (len₀ : Prop) : Prop :=
  len₀

@[qualif]
def EqFalse (len₀ : Prop) : Prop :=
  (¬len₀)

@[qualif]
def EqZero (len₀ : Int) : Prop :=
  (len₀ = 0)

@[qualif]
def GtZero (len₀ : Int) : Prop :=
  (len₀ > 0)

@[qualif]
def GeZero (len₀ : Int) : Prop :=
  (len₀ ≥ 0)

@[qualif]
def LtZero (len₀ : Int) : Prop :=
  (len₀ < 0)

@[qualif]
def LeZero (len₀ : Int) : Prop :=
  (len₀ ≤ 0)

@[qualif]
def Eq (len₀ : Int) (a'₁ : Int) : Prop :=
  (len₀ = a'₁)

@[qualif]
def Gt (len₀ : Int) (a'₁ : Int) : Prop :=
  (len₀ > a'₁)

@[qualif]
def Ge (len₀ : Int) (a'₁ : Int) : Prop :=
  (len₀ ≥ a'₁)

@[qualif]
def Lt (len₀ : Int) (a'₁ : Int) : Prop :=
  (len₀ < a'₁)

@[qualif]
def Le (len₀ : Int) (a'₁ : Int) : Prop :=
  (len₀ ≤ a'₁)

@[qualif]
def Le1 (len₀ : Int) (a'₁ : Int) : Prop :=
  (len₀ ≤ (a'₁ - 1))

end Test01Qualifs

open Test01Qualifs

set_option maxHeartbeats 5000000
#time def Test01_proof : Test01 := by
  unfold Test01
  solve_fixpoint_combo

end F
