import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test
open Classical

namespace F

namespace TestQualifs

@[qualif]
def EqTrue (ptr₀ : Prop) : Prop :=
  ptr₀

@[qualif]
def EqFalse (ptr₀ : Prop) : Prop :=
  (¬ptr₀)

@[qualif]
def EqZero (ptr₀ : Int) : Prop :=
  (ptr₀ = 0)

@[qualif]
def GtZero (ptr₀ : Int) : Prop :=
  (ptr₀ > 0)

@[qualif]
def GeZero (ptr₀ : Int) : Prop :=
  (ptr₀ ≥ 0)

@[qualif]
def LtZero (ptr₀ : Int) : Prop :=
  (ptr₀ < 0)

@[qualif]
def LeZero (ptr₀ : Int) : Prop :=
  (ptr₀ ≤ 0)

@[qualif]
def Eq (ptr₀ : Int) (p₀ : Int) : Prop :=
  (ptr₀ = p₀)

@[qualif]
def Gt (ptr₀ : Int) (p₀ : Int) : Prop :=
  (ptr₀ > p₀)

@[qualif]
def Ge (ptr₀ : Int) (p₀ : Int) : Prop :=
  (ptr₀ ≥ p₀)

@[qualif]
def Lt (ptr₀ : Int) (p₀ : Int) : Prop :=
  (ptr₀ < p₀)

@[qualif]
def Le (ptr₀ : Int) (p₀ : Int) : Prop :=
  (ptr₀ ≤ p₀)

@[qualif]
def Le1 (ptr₀ : Int) (p₀ : Int) : Prop :=
  (ptr₀ ≤ (p₀ - 1))

end TestQualifs

open TestQualifs

set_option maxHeartbeats 5000000
def Test_proof : Test := by
  unfold Test
  try solve_fixpoint

end F
