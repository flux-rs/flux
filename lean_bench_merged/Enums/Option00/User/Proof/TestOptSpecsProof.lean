import LeanFixpoint
import Enums.Option00.Flux.Prelude
import Enums.Option00.Flux.VC.TestOptSpecs
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestOptSpecsQualifs

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
def Eq (a'₀ : Int) (c₀ : Int) : Prop :=
  (a'₀ = c₀)

@[qualif]
def Gt (a'₀ : Int) (c₀ : Int) : Prop :=
  (a'₀ > c₀)

@[qualif]
def Ge (a'₀ : Int) (c₀ : Int) : Prop :=
  (a'₀ ≥ c₀)

@[qualif]
def Lt (a'₀ : Int) (c₀ : Int) : Prop :=
  (a'₀ < c₀)

@[qualif]
def Le (a'₀ : Int) (c₀ : Int) : Prop :=
  (a'₀ ≤ c₀)

@[qualif]
def Le1 (a'₀ : Int) (c₀ : Int) : Prop :=
  (a'₀ ≤ (c₀ - 1))

end TestOptSpecsQualifs

open TestOptSpecsQualifs

set_option maxHeartbeats 5000000
#time def TestOptSpecs_proof : TestOptSpecs := by
  unfold TestOptSpecs
  solve_fixpoint_combo

end F
