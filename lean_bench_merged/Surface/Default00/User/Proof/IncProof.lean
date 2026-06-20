import LeanFixpoint
import Surface.Default00.Flux.Prelude
import Surface.Default00.Flux.VC.Inc
open Classical
set_option linter.unusedVariables false


namespace F

namespace IncQualifs

@[qualif]
def EqTrue (y₀ : Prop) : Prop :=
  y₀

@[qualif]
def EqFalse (y₀ : Prop) : Prop :=
  (¬y₀)

@[qualif]
def EqZero (y₀ : Int) : Prop :=
  (y₀ = 0)

@[qualif]
def GtZero (y₀ : Int) : Prop :=
  (y₀ > 0)

@[qualif]
def GeZero (y₀ : Int) : Prop :=
  (y₀ ≥ 0)

@[qualif]
def LtZero (y₀ : Int) : Prop :=
  (y₀ < 0)

@[qualif]
def LeZero (y₀ : Int) : Prop :=
  (y₀ ≤ 0)

@[qualif]
def Eq (y₀ : Int) (a'₁ : Int) : Prop :=
  (y₀ = a'₁)

@[qualif]
def Gt (y₀ : Int) (a'₁ : Int) : Prop :=
  (y₀ > a'₁)

@[qualif]
def Ge (y₀ : Int) (a'₁ : Int) : Prop :=
  (y₀ ≥ a'₁)

@[qualif]
def Lt (y₀ : Int) (a'₁ : Int) : Prop :=
  (y₀ < a'₁)

@[qualif]
def Le (y₀ : Int) (a'₁ : Int) : Prop :=
  (y₀ ≤ a'₁)

@[qualif]
def Le1 (y₀ : Int) (a'₁ : Int) : Prop :=
  (y₀ ≤ (a'₁ - 1))

end IncQualifs

open IncQualifs

set_option maxHeartbeats 5000000
#time def Inc_proof : Inc := by
  unfold Inc
  solve_fixpoint_combo

end F
