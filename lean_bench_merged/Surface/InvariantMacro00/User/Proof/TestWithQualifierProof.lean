import LeanFixpoint
import Surface.InvariantMacro00.Flux.Prelude
import Surface.InvariantMacro00.Flux.VC.TestWithQualifier
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestWithQualifierQualifs

@[qualif]
def Auto_240_244 (a'₂ : Int) (a'₃ : Int) (a'₄ : Int) : Prop :=
  ((((a'₂ + a'₄) = a'₃) ∧ (a'₄ ≥ (99 - 99))) ∧ (a'₂ ≥ (66 - 66)))

@[qualif]
def EqTrue (i₀ : Prop) : Prop :=
  i₀

@[qualif]
def EqFalse (i₀ : Prop) : Prop :=
  (¬i₀)

@[qualif]
def EqZero (i₀ : Int) : Prop :=
  (i₀ = 0)

@[qualif]
def GtZero (i₀ : Int) : Prop :=
  (i₀ > 0)

@[qualif]
def GeZero (i₀ : Int) : Prop :=
  (i₀ ≥ 0)

@[qualif]
def LtZero (i₀ : Int) : Prop :=
  (i₀ < 0)

@[qualif]
def LeZero (i₀ : Int) : Prop :=
  (i₀ ≤ 0)

@[qualif]
def Eq (i₀ : Int) (res₀ : Int) : Prop :=
  (i₀ = res₀)

@[qualif]
def Gt (i₀ : Int) (res₀ : Int) : Prop :=
  (i₀ > res₀)

@[qualif]
def Ge (i₀ : Int) (res₀ : Int) : Prop :=
  (i₀ ≥ res₀)

@[qualif]
def Lt (i₀ : Int) (res₀ : Int) : Prop :=
  (i₀ < res₀)

@[qualif]
def Le (i₀ : Int) (res₀ : Int) : Prop :=
  (i₀ ≤ res₀)

@[qualif]
def Le1 (i₀ : Int) (res₀ : Int) : Prop :=
  (i₀ ≤ (res₀ - 1))

end TestWithQualifierQualifs

open TestWithQualifierQualifs

set_option maxHeartbeats 5000000
#time def TestWithQualifier_proof : TestWithQualifier := by
  unfold TestWithQualifier
  solve_fixpoint_combo

end F
