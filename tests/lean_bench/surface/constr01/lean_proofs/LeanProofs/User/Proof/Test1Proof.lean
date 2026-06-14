import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test1
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test1Qualifs

@[qualif]
def EqTrue (foo₀ : Prop) : Prop :=
  foo₀

@[qualif]
def EqFalse (foo₀ : Prop) : Prop :=
  (¬foo₀)

@[qualif]
def EqZero (foo₀ : Int) : Prop :=
  (foo₀ = 0)

@[qualif]
def GtZero (foo₀ : Int) : Prop :=
  (foo₀ > 0)

@[qualif]
def GeZero (foo₀ : Int) : Prop :=
  (foo₀ ≥ 0)

@[qualif]
def LtZero (foo₀ : Int) : Prop :=
  (foo₀ < 0)

@[qualif]
def LeZero (foo₀ : Int) : Prop :=
  (foo₀ ≤ 0)

@[qualif]
def Eq (foo₀ : Int) (a'₁ : Int) : Prop :=
  (foo₀ = a'₁)

@[qualif]
def Gt (foo₀ : Int) (a'₁ : Int) : Prop :=
  (foo₀ > a'₁)

@[qualif]
def Ge (foo₀ : Int) (a'₁ : Int) : Prop :=
  (foo₀ ≥ a'₁)

@[qualif]
def Lt (foo₀ : Int) (a'₁ : Int) : Prop :=
  (foo₀ < a'₁)

@[qualif]
def Le (foo₀ : Int) (a'₁ : Int) : Prop :=
  (foo₀ ≤ a'₁)

@[qualif]
def Le1 (foo₀ : Int) (a'₁ : Int) : Prop :=
  (foo₀ ≤ (a'₁ - 1))

end Test1Qualifs

open Test1Qualifs

set_option maxHeartbeats 5000000
def Test1_proof : Test1 := by
  unfold Test1
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
