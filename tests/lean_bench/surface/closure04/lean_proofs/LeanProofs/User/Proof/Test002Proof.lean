import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test002
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test002Qualifs

@[qualif]
def EqTrue (frog₀ : Prop) : Prop :=
  frog₀

@[qualif]
def EqFalse (frog₀ : Prop) : Prop :=
  (¬frog₀)

@[qualif]
def EqZero (frog₀ : Int) : Prop :=
  (frog₀ = 0)

@[qualif]
def GtZero (frog₀ : Int) : Prop :=
  (frog₀ > 0)

@[qualif]
def GeZero (frog₀ : Int) : Prop :=
  (frog₀ ≥ 0)

@[qualif]
def LtZero (frog₀ : Int) : Prop :=
  (frog₀ < 0)

@[qualif]
def LeZero (frog₀ : Int) : Prop :=
  (frog₀ ≤ 0)

@[qualif]
def Eq (frog₀ : Int) (a'₁ : Int) : Prop :=
  (frog₀ = a'₁)

@[qualif]
def Gt (frog₀ : Int) (a'₁ : Int) : Prop :=
  (frog₀ > a'₁)

@[qualif]
def Ge (frog₀ : Int) (a'₁ : Int) : Prop :=
  (frog₀ ≥ a'₁)

@[qualif]
def Lt (frog₀ : Int) (a'₁ : Int) : Prop :=
  (frog₀ < a'₁)

@[qualif]
def Le (frog₀ : Int) (a'₁ : Int) : Prop :=
  (frog₀ ≤ a'₁)

@[qualif]
def Le1 (frog₀ : Int) (a'₁ : Int) : Prop :=
  (frog₀ ≤ (a'₁ - 1))

end Test002Qualifs

open Test002Qualifs

set_option maxHeartbeats 5000000
def Test002_proof : Test002 := by
  unfold Test002
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
