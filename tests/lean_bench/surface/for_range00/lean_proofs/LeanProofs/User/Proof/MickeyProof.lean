import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Mickey
open Classical

namespace F

namespace MickeyQualifs

@[qualif]
def EqTrue (iter₀ : Prop) : Prop :=
  iter₀

@[qualif]
def EqFalse (iter₀ : Prop) : Prop :=
  (¬iter₀)

@[qualif]
def EqZero (iter₀ : Int) : Prop :=
  (iter₀ = 0)

@[qualif]
def GtZero (iter₀ : Int) : Prop :=
  (iter₀ > 0)

@[qualif]
def GeZero (iter₀ : Int) : Prop :=
  (iter₀ ≥ 0)

@[qualif]
def LtZero (iter₀ : Int) : Prop :=
  (iter₀ < 0)

@[qualif]
def LeZero (iter₀ : Int) : Prop :=
  (iter₀ ≤ 0)

@[qualif]
def Eq (iter₀ : Int) (r₀ : Int) : Prop :=
  (iter₀ = r₀)

@[qualif]
def Gt (iter₀ : Int) (r₀ : Int) : Prop :=
  (iter₀ > r₀)

@[qualif]
def Ge (iter₀ : Int) (r₀ : Int) : Prop :=
  (iter₀ ≥ r₀)

@[qualif]
def Lt (iter₀ : Int) (r₀ : Int) : Prop :=
  (iter₀ < r₀)

@[qualif]
def Le (iter₀ : Int) (r₀ : Int) : Prop :=
  (iter₀ ≤ r₀)

@[qualif]
def Le1 (iter₀ : Int) (r₀ : Int) : Prop :=
  (iter₀ ≤ (r₀ - 1))

end MickeyQualifs

open MickeyQualifs

set_option maxHeartbeats 5000000
def Mickey_proof : Mickey := by
  unfold Mickey
  try solve_fixpoint

end F
