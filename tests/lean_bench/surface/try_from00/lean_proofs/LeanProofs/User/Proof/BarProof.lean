import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Bar
open Classical
set_option linter.unusedVariables false


namespace F

namespace BarQualifs

@[qualif]
def EqTrue (my_num₀ : Prop) : Prop :=
  my_num₀

@[qualif]
def EqFalse (my_num₀ : Prop) : Prop :=
  (¬my_num₀)

@[qualif]
def EqZero (my_num₀ : Int) : Prop :=
  (my_num₀ = 0)

@[qualif]
def GtZero (my_num₀ : Int) : Prop :=
  (my_num₀ > 0)

@[qualif]
def GeZero (my_num₀ : Int) : Prop :=
  (my_num₀ ≥ 0)

@[qualif]
def LtZero (my_num₀ : Int) : Prop :=
  (my_num₀ < 0)

@[qualif]
def LeZero (my_num₀ : Int) : Prop :=
  (my_num₀ ≤ 0)

@[qualif]
def Eq (my_num₀ : Int) (a'₁ : Int) : Prop :=
  (my_num₀ = a'₁)

@[qualif]
def Gt (my_num₀ : Int) (a'₁ : Int) : Prop :=
  (my_num₀ > a'₁)

@[qualif]
def Ge (my_num₀ : Int) (a'₁ : Int) : Prop :=
  (my_num₀ ≥ a'₁)

@[qualif]
def Lt (my_num₀ : Int) (a'₁ : Int) : Prop :=
  (my_num₀ < a'₁)

@[qualif]
def Le (my_num₀ : Int) (a'₁ : Int) : Prop :=
  (my_num₀ ≤ a'₁)

@[qualif]
def Le1 (my_num₀ : Int) (a'₁ : Int) : Prop :=
  (my_num₀ ≤ (a'₁ - 1))

end BarQualifs

open BarQualifs

set_option maxHeartbeats 5000000
def Bar_proof : Bar := by
  unfold Bar
  solve_fixpoint_combo

end F
