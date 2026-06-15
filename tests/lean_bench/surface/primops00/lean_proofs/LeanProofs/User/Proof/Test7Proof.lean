import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test7
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test7Qualifs

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
def Eq (b₀ : Int) (m₀ : Int) : Prop :=
  (b₀ = m₀)

@[qualif]
def Gt (b₀ : Int) (m₀ : Int) : Prop :=
  (b₀ > m₀)

@[qualif]
def Ge (b₀ : Int) (m₀ : Int) : Prop :=
  (b₀ ≥ m₀)

@[qualif]
def Lt (b₀ : Int) (m₀ : Int) : Prop :=
  (b₀ < m₀)

@[qualif]
def Le (b₀ : Int) (m₀ : Int) : Prop :=
  (b₀ ≤ m₀)

@[qualif]
def Le1 (b₀ : Int) (m₀ : Int) : Prop :=
  (b₀ ≤ (m₀ - 1))

end Test7Qualifs

open Test7Qualifs

set_option maxHeartbeats 5000000
def Test7_proof : Test7 := by
  unfold Test7
  solve_fixpoint_combo

end F
