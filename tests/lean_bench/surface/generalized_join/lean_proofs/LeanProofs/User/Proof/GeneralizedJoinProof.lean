import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.GeneralizedJoin
open Classical

namespace F

namespace GeneralizedJoinQualifs

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
def Eq (n₀ : Int) (j₀ : Int) : Prop :=
  (n₀ = j₀)

@[qualif]
def Gt (n₀ : Int) (j₀ : Int) : Prop :=
  (n₀ > j₀)

@[qualif]
def Ge (n₀ : Int) (j₀ : Int) : Prop :=
  (n₀ ≥ j₀)

@[qualif]
def Lt (n₀ : Int) (j₀ : Int) : Prop :=
  (n₀ < j₀)

@[qualif]
def Le (n₀ : Int) (j₀ : Int) : Prop :=
  (n₀ ≤ j₀)

@[qualif]
def Le1 (n₀ : Int) (j₀ : Int) : Prop :=
  (n₀ ≤ (j₀ - 1))

end GeneralizedJoinQualifs

open GeneralizedJoinQualifs

set_option maxHeartbeats 5000000
def GeneralizedJoin_proof : GeneralizedJoin := by
  unfold GeneralizedJoin
  try solve_fixpoint

end F
