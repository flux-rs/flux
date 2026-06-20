import LeanFixpoint
import Surface.Closure12.Flux.Prelude
import Surface.Closure12.Flux.VC.TestForeach
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestForeachQualifs

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
def Eq (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ = item₀)

@[qualif]
def Gt (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ > item₀)

@[qualif]
def Ge (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ ≥ item₀)

@[qualif]
def Lt (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ < item₀)

@[qualif]
def Le (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ ≤ item₀)

@[qualif]
def Le1 (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ ≤ (item₀ - 1))

end TestForeachQualifs

open TestForeachQualifs

set_option maxHeartbeats 5000000
#time def TestForeach_proof : TestForeach := by
  unfold TestForeach
  solve_fixpoint_combo

end F
