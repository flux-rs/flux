import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test
open Classical

namespace F

namespace TestQualifs

@[qualif]
def EqTrue (token₀ : Prop) : Prop :=
  token₀

@[qualif]
def EqFalse (token₀ : Prop) : Prop :=
  (¬token₀)

@[qualif]
def EqZero (token₀ : Int) : Prop :=
  (token₀ = 0)

@[qualif]
def GtZero (token₀ : Int) : Prop :=
  (token₀ > 0)

@[qualif]
def GeZero (token₀ : Int) : Prop :=
  (token₀ ≥ 0)

@[qualif]
def LtZero (token₀ : Int) : Prop :=
  (token₀ < 0)

@[qualif]
def LeZero (token₀ : Int) : Prop :=
  (token₀ ≤ 0)

@[qualif]
def Eq (token₀ : Int) (a'₁ : Int) : Prop :=
  (token₀ = a'₁)

@[qualif]
def Gt (token₀ : Int) (a'₁ : Int) : Prop :=
  (token₀ > a'₁)

@[qualif]
def Ge (token₀ : Int) (a'₁ : Int) : Prop :=
  (token₀ ≥ a'₁)

@[qualif]
def Lt (token₀ : Int) (a'₁ : Int) : Prop :=
  (token₀ < a'₁)

@[qualif]
def Le (token₀ : Int) (a'₁ : Int) : Prop :=
  (token₀ ≤ a'₁)

@[qualif]
def Le1 (token₀ : Int) (a'₁ : Int) : Prop :=
  (token₀ ≤ (a'₁ - 1))

end TestQualifs

open TestQualifs

set_option maxHeartbeats 5000000
def Test_proof : Test := by
  unfold Test
  try solve_fixpoint

end F
