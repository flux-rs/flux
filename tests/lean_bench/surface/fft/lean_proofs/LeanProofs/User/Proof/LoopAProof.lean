import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LoopA
open Classical
set_option linter.unusedVariables false


namespace F

namespace LoopAQualifs

@[qualif]
def EqTrue (n2₀ : Prop) : Prop :=
  n2₀

@[qualif]
def EqFalse (n2₀ : Prop) : Prop :=
  (¬n2₀)

@[qualif]
def EqZero (n2₀ : Int) : Prop :=
  (n2₀ = 0)

@[qualif]
def GtZero (n2₀ : Int) : Prop :=
  (n2₀ > 0)

@[qualif]
def GeZero (n2₀ : Int) : Prop :=
  (n2₀ ≥ 0)

@[qualif]
def LtZero (n2₀ : Int) : Prop :=
  (n2₀ < 0)

@[qualif]
def LeZero (n2₀ : Int) : Prop :=
  (n2₀ ≤ 0)

@[qualif]
def Eq (n2₀ : Int) (n4₀ : Int) : Prop :=
  (n2₀ = n4₀)

@[qualif]
def Gt (n2₀ : Int) (n4₀ : Int) : Prop :=
  (n2₀ > n4₀)

@[qualif]
def Ge (n2₀ : Int) (n4₀ : Int) : Prop :=
  (n2₀ ≥ n4₀)

@[qualif]
def Lt (n2₀ : Int) (n4₀ : Int) : Prop :=
  (n2₀ < n4₀)

@[qualif]
def Le (n2₀ : Int) (n4₀ : Int) : Prop :=
  (n2₀ ≤ n4₀)

@[qualif]
def Le1 (n2₀ : Int) (n4₀ : Int) : Prop :=
  (n2₀ ≤ (n4₀ - 1))

end LoopAQualifs

open LoopAQualifs

set_option maxHeartbeats 5000000
def LoopA_proof : LoopA := by
  unfold LoopA
  solve_fixpoint_combo

end F
