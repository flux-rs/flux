import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test03F
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test03FQualifs

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
def Eq (b₀ : Int) (a₀ : Int) : Prop :=
  (b₀ = a₀)

@[qualif]
def Gt (b₀ : Int) (a₀ : Int) : Prop :=
  (b₀ > a₀)

@[qualif]
def Ge (b₀ : Int) (a₀ : Int) : Prop :=
  (b₀ ≥ a₀)

@[qualif]
def Lt (b₀ : Int) (a₀ : Int) : Prop :=
  (b₀ < a₀)

@[qualif]
def Le (b₀ : Int) (a₀ : Int) : Prop :=
  (b₀ ≤ a₀)

@[qualif]
def Le1 (b₀ : Int) (a₀ : Int) : Prop :=
  (b₀ ≤ (a₀ - 1))

end Test03FQualifs

open Test03FQualifs

set_option maxHeartbeats 5000000
#time def Test03F_proof : Test03F := by
  unfold Test03F
  solve_fixpoint_combo

end F
