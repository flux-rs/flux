import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestAndThenNonePropagates
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestAndThenNonePropagatesQualifs

@[qualif]
def EqTrue (x₀ : Prop) : Prop :=
  x₀

@[qualif]
def EqFalse (x₀ : Prop) : Prop :=
  (¬x₀)

@[qualif]
def EqZero (x₀ : Int) : Prop :=
  (x₀ = 0)

@[qualif]
def GtZero (x₀ : Int) : Prop :=
  (x₀ > 0)

@[qualif]
def GeZero (x₀ : Int) : Prop :=
  (x₀ ≥ 0)

@[qualif]
def LtZero (x₀ : Int) : Prop :=
  (x₀ < 0)

@[qualif]
def LeZero (x₀ : Int) : Prop :=
  (x₀ ≤ 0)

@[qualif]
def Eq (x₀ : Int) (result₀ : Int) : Prop :=
  (x₀ = result₀)

@[qualif]
def Gt (x₀ : Int) (result₀ : Int) : Prop :=
  (x₀ > result₀)

@[qualif]
def Ge (x₀ : Int) (result₀ : Int) : Prop :=
  (x₀ ≥ result₀)

@[qualif]
def Lt (x₀ : Int) (result₀ : Int) : Prop :=
  (x₀ < result₀)

@[qualif]
def Le (x₀ : Int) (result₀ : Int) : Prop :=
  (x₀ ≤ result₀)

@[qualif]
def Le1 (x₀ : Int) (result₀ : Int) : Prop :=
  (x₀ ≤ (result₀ - 1))

end TestAndThenNonePropagatesQualifs

open TestAndThenNonePropagatesQualifs

set_option maxHeartbeats 5000000
def TestAndThenNonePropagates_proof : TestAndThenNonePropagates := by
  unfold TestAndThenNonePropagates
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
