import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WriteIx
open Classical
set_option linter.unusedVariables false


namespace F

namespace WriteIxQualifs

@[qualif]
def EqTrue (value₀ : Prop) : Prop :=
  value₀

@[qualif]
def EqFalse (value₀ : Prop) : Prop :=
  (¬value₀)

@[qualif]
def EqZero (value₀ : Int) : Prop :=
  (value₀ = 0)

@[qualif]
def GtZero (value₀ : Int) : Prop :=
  (value₀ > 0)

@[qualif]
def GeZero (value₀ : Int) : Prop :=
  (value₀ ≥ 0)

@[qualif]
def LtZero (value₀ : Int) : Prop :=
  (value₀ < 0)

@[qualif]
def LeZero (value₀ : Int) : Prop :=
  (value₀ ≤ 0)

@[qualif]
def Eq (value₀ : Int) (a'₁ : Int) : Prop :=
  (value₀ = a'₁)

@[qualif]
def Gt (value₀ : Int) (a'₁ : Int) : Prop :=
  (value₀ > a'₁)

@[qualif]
def Ge (value₀ : Int) (a'₁ : Int) : Prop :=
  (value₀ ≥ a'₁)

@[qualif]
def Lt (value₀ : Int) (a'₁ : Int) : Prop :=
  (value₀ < a'₁)

@[qualif]
def Le (value₀ : Int) (a'₁ : Int) : Prop :=
  (value₀ ≤ a'₁)

@[qualif]
def Le1 (value₀ : Int) (a'₁ : Int) : Prop :=
  (value₀ ≤ (a'₁ - 1))

end WriteIxQualifs

open WriteIxQualifs

set_option maxHeartbeats 5000000
def WriteIx_proof : WriteIx := by
  unfold WriteIx
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
