import LeanFixpoint
import Surface.Bitvec03.Flux.Prelude
import Surface.Bitvec03.Flux.VC.TestOrB
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestOrBQualifs

@[qualif]
def EqTrue (a'₀ : Prop) : Prop :=
  a'₀

@[qualif]
def EqFalse (a'₀ : Prop) : Prop :=
  (¬a'₀)

@[qualif]
def EqZero (a'₀ : Int) : Prop :=
  (a'₀ = 0)

@[qualif]
def GtZero (a'₀ : Int) : Prop :=
  (a'₀ > 0)

@[qualif]
def GeZero (a'₀ : Int) : Prop :=
  (a'₀ ≥ 0)

@[qualif]
def LtZero (a'₀ : Int) : Prop :=
  (a'₀ < 0)

@[qualif]
def LeZero (a'₀ : Int) : Prop :=
  (a'₀ ≤ 0)

@[qualif]
def Eq (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ = a'₁)

@[qualif]
def Gt (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ > a'₁)

@[qualif]
def Ge (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ ≥ a'₁)

@[qualif]
def Lt (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ < a'₁)

@[qualif]
def Le (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ ≤ a'₁)

@[qualif]
def Le1 (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ ≤ (a'₁ - 1))

end TestOrBQualifs

open TestOrBQualifs

set_option maxHeartbeats 5000000
#time def TestOrB_proof : TestOrB := by
  unfold TestOrB
  solve_fixpoint_combo

end F
