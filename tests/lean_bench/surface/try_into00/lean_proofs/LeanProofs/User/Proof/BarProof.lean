import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Bar
open Classical
set_option linter.unusedVariables false


namespace F

namespace BarQualifs

@[qualif]
def EqTrue (n₀ : Prop) : Prop :=
  n₀

@[qualif]
def EqFalse (n₀ : Prop) : Prop :=
  (¬n₀)

@[qualif]
def EqZero (n₀ : Int) : Prop :=
  (n₀ = 0)

@[qualif]
def GtZero (n₀ : Int) : Prop :=
  (n₀ > 0)

@[qualif]
def GeZero (n₀ : Int) : Prop :=
  (n₀ ≥ 0)

@[qualif]
def LtZero (n₀ : Int) : Prop :=
  (n₀ < 0)

@[qualif]
def LeZero (n₀ : Int) : Prop :=
  (n₀ ≤ 0)

@[qualif]
def Eq (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ = a'₁)

@[qualif]
def Gt (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ > a'₁)

@[qualif]
def Ge (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ ≥ a'₁)

@[qualif]
def Lt (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ < a'₁)

@[qualif]
def Le (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ ≤ a'₁)

@[qualif]
def Le1 (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ ≤ (a'₁ - 1))

end BarQualifs

open BarQualifs

set_option maxHeartbeats 5000000
#time def Bar_proof : Bar := by
  unfold Bar
  solve_fixpoint_combo

end F
