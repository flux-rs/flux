import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test2
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test2Qualifs

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
def Eq (b₀ : Int) (s₀ : Int) : Prop :=
  (b₀ = s₀)

@[qualif]
def Gt (b₀ : Int) (s₀ : Int) : Prop :=
  (b₀ > s₀)

@[qualif]
def Ge (b₀ : Int) (s₀ : Int) : Prop :=
  (b₀ ≥ s₀)

@[qualif]
def Lt (b₀ : Int) (s₀ : Int) : Prop :=
  (b₀ < s₀)

@[qualif]
def Le (b₀ : Int) (s₀ : Int) : Prop :=
  (b₀ ≤ s₀)

@[qualif]
def Le1 (b₀ : Int) (s₀ : Int) : Prop :=
  (b₀ ≤ (s₀ - 1))

end Test2Qualifs

open Test2Qualifs

set_option maxHeartbeats 5000000
#time def Test2_proof : Test2 := by
  unfold Test2
  solve_fixpoint_combo

end F
