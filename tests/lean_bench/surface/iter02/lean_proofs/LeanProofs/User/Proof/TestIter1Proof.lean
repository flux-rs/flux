import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestIter1
open Classical

namespace F

namespace TestIter1Qualifs

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
def Eq (n₀ : Int) (next_s₀ : Int) : Prop :=
  (n₀ = next_s₀)

@[qualif]
def Gt (n₀ : Int) (next_s₀ : Int) : Prop :=
  (n₀ > next_s₀)

@[qualif]
def Ge (n₀ : Int) (next_s₀ : Int) : Prop :=
  (n₀ ≥ next_s₀)

@[qualif]
def Lt (n₀ : Int) (next_s₀ : Int) : Prop :=
  (n₀ < next_s₀)

@[qualif]
def Le (n₀ : Int) (next_s₀ : Int) : Prop :=
  (n₀ ≤ next_s₀)

@[qualif]
def Le1 (n₀ : Int) (next_s₀ : Int) : Prop :=
  (n₀ ≤ (next_s₀ - 1))

end TestIter1Qualifs

open TestIter1Qualifs

def TestIter1_proof : TestIter1 := by
  unfold TestIter1
  try solve_fixpoint

end F
