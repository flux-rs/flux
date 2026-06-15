import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__1__Next
open Classical
set_option linter.unusedVariables false


namespace F

namespace Impl1NextQualifs

@[qualif]
def EqTrue (v₀ : Prop) : Prop :=
  v₀

@[qualif]
def EqFalse (v₀ : Prop) : Prop :=
  (¬v₀)

@[qualif]
def EqZero (v₀ : Int) : Prop :=
  (v₀ = 0)

@[qualif]
def GtZero (v₀ : Int) : Prop :=
  (v₀ > 0)

@[qualif]
def GeZero (v₀ : Int) : Prop :=
  (v₀ ≥ 0)

@[qualif]
def LtZero (v₀ : Int) : Prop :=
  (v₀ < 0)

@[qualif]
def LeZero (v₀ : Int) : Prop :=
  (v₀ ≤ 0)

@[qualif]
def Eq (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ = a'₁)

@[qualif]
def Gt (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ > a'₁)

@[qualif]
def Ge (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ ≥ a'₁)

@[qualif]
def Lt (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ < a'₁)

@[qualif]
def Le (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ ≤ a'₁)

@[qualif]
def Le1 (v₀ : Int) (a'₁ : Int) : Prop :=
  (v₀ ≤ (a'₁ - 1))

end Impl1NextQualifs

open Impl1NextQualifs

set_option maxHeartbeats 5000000
def Impl__1__Next_proof : Impl__1__Next := by
  unfold Impl__1__Next
  solve_fixpoint_combo

end F
