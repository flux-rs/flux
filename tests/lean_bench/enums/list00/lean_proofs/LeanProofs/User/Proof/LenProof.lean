import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Len
open Classical
set_option linter.unusedVariables false


namespace F

namespace LenQualifs

@[qualif]
def EqTrue (n₁ : Prop) : Prop :=
  n₁

@[qualif]
def EqFalse (n₁ : Prop) : Prop :=
  (¬n₁)

@[qualif]
def EqZero (n₁ : Int) : Prop :=
  (n₁ = 0)

@[qualif]
def GtZero (n₁ : Int) : Prop :=
  (n₁ > 0)

@[qualif]
def GeZero (n₁ : Int) : Prop :=
  (n₁ ≥ 0)

@[qualif]
def LtZero (n₁ : Int) : Prop :=
  (n₁ < 0)

@[qualif]
def LeZero (n₁ : Int) : Prop :=
  (n₁ ≤ 0)

@[qualif]
def Eq (n₁ : Int) (a'₁ : Int) : Prop :=
  (n₁ = a'₁)

@[qualif]
def Gt (n₁ : Int) (a'₁ : Int) : Prop :=
  (n₁ > a'₁)

@[qualif]
def Ge (n₁ : Int) (a'₁ : Int) : Prop :=
  (n₁ ≥ a'₁)

@[qualif]
def Lt (n₁ : Int) (a'₁ : Int) : Prop :=
  (n₁ < a'₁)

@[qualif]
def Le (n₁ : Int) (a'₁ : Int) : Prop :=
  (n₁ ≤ a'₁)

@[qualif]
def Le1 (n₁ : Int) (a'₁ : Int) : Prop :=
  (n₁ ≤ (a'₁ - 1))

end LenQualifs

open LenQualifs

set_option maxHeartbeats 5000000
def Len_proof : Len := by
  unfold Len
  solve_fixpoint_combo

end F
