import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.CloseAtJoin
open Classical

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

def CloseAtJoin_proof : CloseAtJoin := by
  unfold CloseAtJoin
  try solve_fixpoint
  exists False
  simp
  exists False
  exists True, 1
  simp
  exists True
end F
