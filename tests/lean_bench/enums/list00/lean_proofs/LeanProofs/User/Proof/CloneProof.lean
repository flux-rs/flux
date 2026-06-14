import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Clone
open Classical
set_option linter.unusedVariables false


namespace F

namespace CloneQualifs

@[qualif]
def EqTrue (val₀ : Prop) : Prop :=
  val₀

@[qualif]
def EqFalse (val₀ : Prop) : Prop :=
  (¬val₀)

@[qualif]
def EqZero (val₀ : Int) : Prop :=
  (val₀ = 0)

@[qualif]
def GtZero (val₀ : Int) : Prop :=
  (val₀ > 0)

@[qualif]
def GeZero (val₀ : Int) : Prop :=
  (val₀ ≥ 0)

@[qualif]
def LtZero (val₀ : Int) : Prop :=
  (val₀ < 0)

@[qualif]
def LeZero (val₀ : Int) : Prop :=
  (val₀ ≤ 0)

@[qualif]
def Eq (val₀ : Int) (a'₁ : Int) : Prop :=
  (val₀ = a'₁)

@[qualif]
def Gt (val₀ : Int) (a'₁ : Int) : Prop :=
  (val₀ > a'₁)

@[qualif]
def Ge (val₀ : Int) (a'₁ : Int) : Prop :=
  (val₀ ≥ a'₁)

@[qualif]
def Lt (val₀ : Int) (a'₁ : Int) : Prop :=
  (val₀ < a'₁)

@[qualif]
def Le (val₀ : Int) (a'₁ : Int) : Prop :=
  (val₀ ≤ a'₁)

@[qualif]
def Le1 (val₀ : Int) (a'₁ : Int) : Prop :=
  (val₀ ≤ (a'₁ - 1))

end CloneQualifs

open CloneQualifs

set_option maxHeartbeats 5000000
def Clone_proof : Clone := by
  unfold Clone
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
