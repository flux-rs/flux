import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.MkStruct
open Classical
set_option linter.unusedVariables false


namespace F

namespace MkStructQualifs

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
def Eq (x₀ : Int) (y₀ : Int) : Prop :=
  (x₀ = y₀)

@[qualif]
def Gt (x₀ : Int) (y₀ : Int) : Prop :=
  (x₀ > y₀)

@[qualif]
def Ge (x₀ : Int) (y₀ : Int) : Prop :=
  (x₀ ≥ y₀)

@[qualif]
def Lt (x₀ : Int) (y₀ : Int) : Prop :=
  (x₀ < y₀)

@[qualif]
def Le (x₀ : Int) (y₀ : Int) : Prop :=
  (x₀ ≤ y₀)

@[qualif]
def Le1 (x₀ : Int) (y₀ : Int) : Prop :=
  (x₀ ≤ (y₀ - 1))

end MkStructQualifs

open MkStructQualifs

set_option maxHeartbeats 5000000
def MkStruct_proof : MkStruct := by
  unfold MkStruct
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
