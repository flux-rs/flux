import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test00
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test00Qualifs

@[qualif]
def EqTrue (b₀ : Prop) : Prop :=
  b₀

@[qualif]
def EqFalse (b₀ : Prop) : Prop :=
  (¬b₀)

@[qualif]
def EqZero (b₀ : Int) : Prop :=
  (b₀ = 0)

@[qualif]
def GtZero (b₀ : Int) : Prop :=
  (b₀ > 0)

@[qualif]
def GeZero (b₀ : Int) : Prop :=
  (b₀ ≥ 0)

@[qualif]
def LtZero (b₀ : Int) : Prop :=
  (b₀ < 0)

@[qualif]
def LeZero (b₀ : Int) : Prop :=
  (b₀ ≤ 0)

@[qualif]
def Eq (b₀ : Int) (p₀ : Int) : Prop :=
  (b₀ = p₀)

@[qualif]
def Gt (b₀ : Int) (p₀ : Int) : Prop :=
  (b₀ > p₀)

@[qualif]
def Ge (b₀ : Int) (p₀ : Int) : Prop :=
  (b₀ ≥ p₀)

@[qualif]
def Lt (b₀ : Int) (p₀ : Int) : Prop :=
  (b₀ < p₀)

@[qualif]
def Le (b₀ : Int) (p₀ : Int) : Prop :=
  (b₀ ≤ p₀)

@[qualif]
def Le1 (b₀ : Int) (p₀ : Int) : Prop :=
  (b₀ ≤ (p₀ - 1))

end Test00Qualifs

open Test00Qualifs

set_option maxHeartbeats 5000000
def Test00_proof : Test00 := by
  unfold Test00
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
