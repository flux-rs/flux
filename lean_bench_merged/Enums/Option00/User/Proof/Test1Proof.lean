import LeanFixpoint
import Enums.Option00.Flux.Prelude
import Enums.Option00.Flux.VC.Test1
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test1Qualifs

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
def Eq (a'₀ : Int) (y₀ : Int) : Prop :=
  (a'₀ = y₀)

@[qualif]
def Gt (a'₀ : Int) (y₀ : Int) : Prop :=
  (a'₀ > y₀)

@[qualif]
def Ge (a'₀ : Int) (y₀ : Int) : Prop :=
  (a'₀ ≥ y₀)

@[qualif]
def Lt (a'₀ : Int) (y₀ : Int) : Prop :=
  (a'₀ < y₀)

@[qualif]
def Le (a'₀ : Int) (y₀ : Int) : Prop :=
  (a'₀ ≤ y₀)

@[qualif]
def Le1 (a'₀ : Int) (y₀ : Int) : Prop :=
  (a'₀ ≤ (y₀ - 1))

end Test1Qualifs

open Test1Qualifs

set_option maxHeartbeats 5000000
#time def Test1_proof : Test1 := by
  unfold Test1
  solve_fixpoint_combo

end F
