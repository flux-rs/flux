import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestSafeDiv
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestSafeDivQualifs

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
def Eq (a'₀ : Int) (res₀ : Int) : Prop :=
  (a'₀ = res₀)

@[qualif]
def Gt (a'₀ : Int) (res₀ : Int) : Prop :=
  (a'₀ > res₀)

@[qualif]
def Ge (a'₀ : Int) (res₀ : Int) : Prop :=
  (a'₀ ≥ res₀)

@[qualif]
def Lt (a'₀ : Int) (res₀ : Int) : Prop :=
  (a'₀ < res₀)

@[qualif]
def Le (a'₀ : Int) (res₀ : Int) : Prop :=
  (a'₀ ≤ res₀)

@[qualif]
def Le1 (a'₀ : Int) (res₀ : Int) : Prop :=
  (a'₀ ≤ (res₀ - 1))

end TestSafeDivQualifs

open TestSafeDivQualifs

set_option maxHeartbeats 5000000
def TestSafeDiv_proof : TestSafeDiv := by
  unfold TestSafeDiv
  try solve_fixpoint

end F
