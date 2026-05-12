import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LoopA
open Classical

namespace F

namespace LoopAQualifs

@[qualif]
def EqTrue (n4₀ : Prop) : Prop :=
  n4₀

@[qualif]
def EqFalse (n4₀ : Prop) : Prop :=
  (¬n4₀)

@[qualif]
def EqZero (n4₀ : Int) : Prop :=
  (n4₀ = 0)

@[qualif]
def GtZero (n4₀ : Int) : Prop :=
  (n4₀ > 0)

@[qualif]
def GeZero (n4₀ : Int) : Prop :=
  (n4₀ ≥ 0)

@[qualif]
def LtZero (n4₀ : Int) : Prop :=
  (n4₀ < 0)

@[qualif]
def LeZero (n4₀ : Int) : Prop :=
  (n4₀ ≤ 0)

@[qualif]
def Eq (n4₀ : Int) (n2₀ : Int) : Prop :=
  (n4₀ = n2₀)

@[qualif]
def Gt (n4₀ : Int) (n2₀ : Int) : Prop :=
  (n4₀ > n2₀)

@[qualif]
def Ge (n4₀ : Int) (n2₀ : Int) : Prop :=
  (n4₀ ≥ n2₀)

@[qualif]
def Lt (n4₀ : Int) (n2₀ : Int) : Prop :=
  (n4₀ < n2₀)

@[qualif]
def Le (n4₀ : Int) (n2₀ : Int) : Prop :=
  (n4₀ ≤ n2₀)

@[qualif]
def Le1 (n4₀ : Int) (n2₀ : Int) : Prop :=
  (n4₀ ≤ (n2₀ - 1))

end LoopAQualifs

open LoopAQualifs

def LoopA_proof : LoopA := by
  unfold LoopA
  try solve_fixpoint

end F
