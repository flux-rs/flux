import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test02
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test02Qualifs

@[qualif]
def EqTrue (n₀ : Prop) : Prop :=
  n₀

@[qualif]
def EqFalse (n₀ : Prop) : Prop :=
  (¬n₀)

@[qualif]
def EqZero (n₀ : Int) : Prop :=
  (n₀ = 0)

@[qualif]
def GtZero (n₀ : Int) : Prop :=
  (n₀ > 0)

@[qualif]
def GeZero (n₀ : Int) : Prop :=
  (n₀ ≥ 0)

@[qualif]
def LtZero (n₀ : Int) : Prop :=
  (n₀ < 0)

@[qualif]
def LeZero (n₀ : Int) : Prop :=
  (n₀ ≤ 0)

@[qualif]
def Eq (n₀ : Int) (v₀ : Int) : Prop :=
  (n₀ = v₀)

@[qualif]
def Gt (n₀ : Int) (v₀ : Int) : Prop :=
  (n₀ > v₀)

@[qualif]
def Ge (n₀ : Int) (v₀ : Int) : Prop :=
  (n₀ ≥ v₀)

@[qualif]
def Lt (n₀ : Int) (v₀ : Int) : Prop :=
  (n₀ < v₀)

@[qualif]
def Le (n₀ : Int) (v₀ : Int) : Prop :=
  (n₀ ≤ v₀)

@[qualif]
def Le1 (n₀ : Int) (v₀ : Int) : Prop :=
  (n₀ ≤ (v₀ - 1))

end Test02Qualifs

open Test02Qualifs

set_option maxHeartbeats 5000000
def Test02_proof : Test02 := by
  unfold Test02
  try solve_fixpoint

end F
