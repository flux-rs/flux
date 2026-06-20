import LeanFixpoint
import Surface.AssocReft06.Flux.Prelude
import Surface.AssocReft06.Flux.VC.AssumeInvariant
open Classical
set_option linter.unusedVariables false


namespace F

namespace AssumeInvariantQualifs

@[qualif]
def EqTrue (s₀ : Prop) : Prop :=
  s₀

@[qualif]
def EqFalse (s₀ : Prop) : Prop :=
  (¬s₀)

@[qualif]
def EqZero (s₀ : Int) : Prop :=
  (s₀ = 0)

@[qualif]
def GtZero (s₀ : Int) : Prop :=
  (s₀ > 0)

@[qualif]
def GeZero (s₀ : Int) : Prop :=
  (s₀ ≥ 0)

@[qualif]
def LtZero (s₀ : Int) : Prop :=
  (s₀ < 0)

@[qualif]
def LeZero (s₀ : Int) : Prop :=
  (s₀ ≤ 0)

@[qualif]
def Eq (s₀ : Int) (a'₁ : Int) : Prop :=
  (s₀ = a'₁)

@[qualif]
def Gt (s₀ : Int) (a'₁ : Int) : Prop :=
  (s₀ > a'₁)

@[qualif]
def Ge (s₀ : Int) (a'₁ : Int) : Prop :=
  (s₀ ≥ a'₁)

@[qualif]
def Lt (s₀ : Int) (a'₁ : Int) : Prop :=
  (s₀ < a'₁)

@[qualif]
def Le (s₀ : Int) (a'₁ : Int) : Prop :=
  (s₀ ≤ a'₁)

@[qualif]
def Le1 (s₀ : Int) (a'₁ : Int) : Prop :=
  (s₀ ≤ (a'₁ - 1))

end AssumeInvariantQualifs

open AssumeInvariantQualifs

set_option maxHeartbeats 5000000
#time def AssumeInvariant_proof : AssumeInvariant := by
  unfold AssumeInvariant
  solve_fixpoint_combo

end F
