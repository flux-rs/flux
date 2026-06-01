import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test
open Classical

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
def Eq (len₀ : Int) (iter₀ : Int) : Prop :=
  (len₀ = iter₀)

@[qualif]
def Gt (len₀ : Int) (iter₀ : Int) : Prop :=
  (len₀ > iter₀)

@[qualif]
def Ge (len₀ : Int) (iter₀ : Int) : Prop :=
  (len₀ ≥ iter₀)

@[qualif]
def Lt (len₀ : Int) (iter₀ : Int) : Prop :=
  (len₀ < iter₀)

@[qualif]
def Le (len₀ : Int) (iter₀ : Int) : Prop :=
  (len₀ ≤ iter₀)

@[qualif]
def Le1 (len₀ : Int) (iter₀ : Int) : Prop :=
  (len₀ ≤ (iter₀ - 1))

end TestQualifs

open TestQualifs

set_option maxHeartbeats 5000000
def Test_proof : Test := by
  unfold Test
  try solve_fixpoint

end F
