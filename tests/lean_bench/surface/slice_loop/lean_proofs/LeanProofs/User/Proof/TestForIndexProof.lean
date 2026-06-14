import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestForIndex
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestForIndexQualifs

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
def Eq (a'₀ : Int) (iter₀ : Int) : Prop :=
  (a'₀ = iter₀)

@[qualif]
def Gt (a'₀ : Int) (iter₀ : Int) : Prop :=
  (a'₀ > iter₀)

@[qualif]
def Ge (a'₀ : Int) (iter₀ : Int) : Prop :=
  (a'₀ ≥ iter₀)

@[qualif]
def Lt (a'₀ : Int) (iter₀ : Int) : Prop :=
  (a'₀ < iter₀)

@[qualif]
def Le (a'₀ : Int) (iter₀ : Int) : Prop :=
  (a'₀ ≤ iter₀)

@[qualif]
def Le1 (a'₀ : Int) (iter₀ : Int) : Prop :=
  (a'₀ ≤ (iter₀ - 1))

end TestForIndexQualifs

open TestForIndexQualifs

set_option maxHeartbeats 5000000
def TestForIndex_proof : TestForIndex := by
  unfold TestForIndex
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
