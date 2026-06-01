import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test6
open Classical

namespace F

namespace Test6Qualifs

@[qualif]
def EqTrue (c₀ : Prop) : Prop :=
  c₀

@[qualif]
def EqFalse (c₀ : Prop) : Prop :=
  (¬c₀)

@[qualif]
def EqZero (c₀ : Int) : Prop :=
  (c₀ = 0)

@[qualif]
def GtZero (c₀ : Int) : Prop :=
  (c₀ > 0)

@[qualif]
def GeZero (c₀ : Int) : Prop :=
  (c₀ ≥ 0)

@[qualif]
def LtZero (c₀ : Int) : Prop :=
  (c₀ < 0)

@[qualif]
def LeZero (c₀ : Int) : Prop :=
  (c₀ ≤ 0)

@[qualif]
def Eq (c₀ : Int) (a'₁ : Int) : Prop :=
  (c₀ = a'₁)

@[qualif]
def Gt (c₀ : Int) (a'₁ : Int) : Prop :=
  (c₀ > a'₁)

@[qualif]
def Ge (c₀ : Int) (a'₁ : Int) : Prop :=
  (c₀ ≥ a'₁)

@[qualif]
def Lt (c₀ : Int) (a'₁ : Int) : Prop :=
  (c₀ < a'₁)

@[qualif]
def Le (c₀ : Int) (a'₁ : Int) : Prop :=
  (c₀ ≤ a'₁)

@[qualif]
def Le1 (c₀ : Int) (a'₁ : Int) : Prop :=
  (c₀ ≤ (a'₁ - 1))

end Test6Qualifs

open Test6Qualifs

set_option maxHeartbeats 5000000
def Test6_proof : Test6 := by
  unfold Test6
  try solve_fixpoint

end F
