import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Goofy
open Classical
set_option linter.unusedVariables false


namespace F

namespace GoofyQualifs

@[qualif]
def EqTrue (thing₀ : Prop) : Prop :=
  thing₀

@[qualif]
def EqFalse (thing₀ : Prop) : Prop :=
  (¬thing₀)

@[qualif]
def EqZero (thing₀ : Int) : Prop :=
  (thing₀ = 0)

@[qualif]
def GtZero (thing₀ : Int) : Prop :=
  (thing₀ > 0)

@[qualif]
def GeZero (thing₀ : Int) : Prop :=
  (thing₀ ≥ 0)

@[qualif]
def LtZero (thing₀ : Int) : Prop :=
  (thing₀ < 0)

@[qualif]
def LeZero (thing₀ : Int) : Prop :=
  (thing₀ ≤ 0)

@[qualif]
def Eq (thing₀ : Int) (thing₁ : Int) : Prop :=
  (thing₀ = thing₁)

@[qualif]
def Gt (thing₀ : Int) (thing₁ : Int) : Prop :=
  (thing₀ > thing₁)

@[qualif]
def Ge (thing₀ : Int) (thing₁ : Int) : Prop :=
  (thing₀ ≥ thing₁)

@[qualif]
def Lt (thing₀ : Int) (thing₁ : Int) : Prop :=
  (thing₀ < thing₁)

@[qualif]
def Le (thing₀ : Int) (thing₁ : Int) : Prop :=
  (thing₀ ≤ thing₁)

@[qualif]
def Le1 (thing₀ : Int) (thing₁ : Int) : Prop :=
  (thing₀ ≤ (thing₁ - 1))

end GoofyQualifs

open GoofyQualifs

set_option maxHeartbeats 5000000
def Goofy_proof : Goofy := by
  unfold Goofy
  solve_fixpoint_combo

end F
