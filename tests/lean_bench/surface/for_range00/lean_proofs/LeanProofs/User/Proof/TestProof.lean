import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestQualifs

@[qualif]
def EqTrue (len₀ : Prop) : Prop :=
  len₀

@[qualif]
def EqFalse (len₀ : Prop) : Prop :=
  (¬len₀)

@[qualif]
def EqZero (len₀ : Int) : Prop :=
  (len₀ = 0)

@[qualif]
def GtZero (len₀ : Int) : Prop :=
  (len₀ > 0)

@[qualif]
def GeZero (len₀ : Int) : Prop :=
  (len₀ ≥ 0)

@[qualif]
def LtZero (len₀ : Int) : Prop :=
  (len₀ < 0)

@[qualif]
def LeZero (len₀ : Int) : Prop :=
  (len₀ ≤ 0)

@[qualif]
def Eq (len₀ : Int) (del₀ : Int) : Prop :=
  (len₀ = del₀)

@[qualif]
def Gt (len₀ : Int) (del₀ : Int) : Prop :=
  (len₀ > del₀)

@[qualif]
def Ge (len₀ : Int) (del₀ : Int) : Prop :=
  (len₀ ≥ del₀)

@[qualif]
def Lt (len₀ : Int) (del₀ : Int) : Prop :=
  (len₀ < del₀)

@[qualif]
def Le (len₀ : Int) (del₀ : Int) : Prop :=
  (len₀ ≤ del₀)

@[qualif]
def Le1 (len₀ : Int) (del₀ : Int) : Prop :=
  (len₀ ≤ (del₀ - 1))

end TestQualifs

open TestQualifs

set_option maxHeartbeats 5000000
def Test_proof : Test := by
  unfold Test
  solve_fixpoint_combo

end F
