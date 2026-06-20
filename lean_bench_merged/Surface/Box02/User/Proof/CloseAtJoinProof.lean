import LeanFixpoint
import Surface.Box02.Flux.Prelude
import Surface.Box02.Flux.VC.CloseAtJoin
open Classical
set_option linter.unusedVariables false


namespace F

namespace CloseAtJoinQualifs

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
def Eq (b₀ : Int) (x₀ : Int) : Prop :=
  (b₀ = x₀)

@[qualif]
def Gt (b₀ : Int) (x₀ : Int) : Prop :=
  (b₀ > x₀)

@[qualif]
def Ge (b₀ : Int) (x₀ : Int) : Prop :=
  (b₀ ≥ x₀)

@[qualif]
def Lt (b₀ : Int) (x₀ : Int) : Prop :=
  (b₀ < x₀)

@[qualif]
def Le (b₀ : Int) (x₀ : Int) : Prop :=
  (b₀ ≤ x₀)

@[qualif]
def Le1 (b₀ : Int) (x₀ : Int) : Prop :=
  (b₀ ≤ (x₀ - 1))

end CloseAtJoinQualifs

open CloseAtJoinQualifs

set_option maxHeartbeats 5000000
#time def CloseAtJoin_proof : CloseAtJoin := by
  unfold CloseAtJoin
  solve_fixpoint_combo

end F
