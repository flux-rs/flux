import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.IncTest
open Classical

namespace F

namespace IncTestQualifs

@[qualif]
def EqTrue (b0₀ : Prop) : Prop :=
  b0₀

@[qualif]
def EqFalse (b0₀ : Prop) : Prop :=
  (¬b0₀)

@[qualif]
def EqZero (b0₀ : Int) : Prop :=
  (b0₀ = 0)

@[qualif]
def GtZero (b0₀ : Int) : Prop :=
  (b0₀ > 0)

@[qualif]
def GeZero (b0₀ : Int) : Prop :=
  (b0₀ ≥ 0)

@[qualif]
def LtZero (b0₀ : Int) : Prop :=
  (b0₀ < 0)

@[qualif]
def LeZero (b0₀ : Int) : Prop :=
  (b0₀ ≤ 0)

@[qualif]
def Eq (b0₀ : Int) (a'₁ : Int) : Prop :=
  (b0₀ = a'₁)

@[qualif]
def Gt (b0₀ : Int) (a'₁ : Int) : Prop :=
  (b0₀ > a'₁)

@[qualif]
def Ge (b0₀ : Int) (a'₁ : Int) : Prop :=
  (b0₀ ≥ a'₁)

@[qualif]
def Lt (b0₀ : Int) (a'₁ : Int) : Prop :=
  (b0₀ < a'₁)

@[qualif]
def Le (b0₀ : Int) (a'₁ : Int) : Prop :=
  (b0₀ ≤ a'₁)

@[qualif]
def Le1 (b0₀ : Int) (a'₁ : Int) : Prop :=
  (b0₀ ≤ (a'₁ - 1))

end IncTestQualifs

open IncTestQualifs

set_option maxHeartbeats 5000000
def IncTest_proof : IncTest := by
  unfold IncTest
  try solve_fixpoint

end F
