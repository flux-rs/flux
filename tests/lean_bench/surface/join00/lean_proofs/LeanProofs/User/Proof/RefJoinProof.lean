import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.RefJoin
open Classical

namespace F

namespace RefJoinQualifs

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
def Eq (b₀ : Int) (r₀ : Int) : Prop :=
  (b₀ = r₀)

@[qualif]
def Gt (b₀ : Int) (r₀ : Int) : Prop :=
  (b₀ > r₀)

@[qualif]
def Ge (b₀ : Int) (r₀ : Int) : Prop :=
  (b₀ ≥ r₀)

@[qualif]
def Lt (b₀ : Int) (r₀ : Int) : Prop :=
  (b₀ < r₀)

@[qualif]
def Le (b₀ : Int) (r₀ : Int) : Prop :=
  (b₀ ≤ r₀)

@[qualif]
def Le1 (b₀ : Int) (r₀ : Int) : Prop :=
  (b₀ ≤ (r₀ - 1))

end RefJoinQualifs

open RefJoinQualifs

set_option maxHeartbeats 5000000
def RefJoin_proof : RefJoin := by
  unfold RefJoin
  try solve_fixpoint

end F
