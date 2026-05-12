import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.NoCloseJoin
open Classical

namespace F

namespace NoCloseJoinQualifs

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

end NoCloseJoinQualifs

open NoCloseJoinQualifs

def NoCloseJoin_proof : NoCloseJoin := by
  unfold NoCloseJoin
  try solve_fixpoint

end F
