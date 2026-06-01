import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test01
open Classical

namespace F

namespace Test01Qualifs

@[qualif]
def EqTrue (i₀ : Prop) : Prop :=
  i₀

@[qualif]
def EqFalse (i₀ : Prop) : Prop :=
  (¬i₀)

@[qualif]
def EqZero (i₀ : Int) : Prop :=
  (i₀ = 0)

@[qualif]
def GtZero (i₀ : Int) : Prop :=
  (i₀ > 0)

@[qualif]
def GeZero (i₀ : Int) : Prop :=
  (i₀ ≥ 0)

@[qualif]
def LtZero (i₀ : Int) : Prop :=
  (i₀ < 0)

@[qualif]
def LeZero (i₀ : Int) : Prop :=
  (i₀ ≤ 0)

@[qualif]
def Eq (i₀ : Int) (p₁ : Int) : Prop :=
  (i₀ = p₁)

@[qualif]
def Gt (i₀ : Int) (p₁ : Int) : Prop :=
  (i₀ > p₁)

@[qualif]
def Ge (i₀ : Int) (p₁ : Int) : Prop :=
  (i₀ ≥ p₁)

@[qualif]
def Lt (i₀ : Int) (p₁ : Int) : Prop :=
  (i₀ < p₁)

@[qualif]
def Le (i₀ : Int) (p₁ : Int) : Prop :=
  (i₀ ≤ p₁)

@[qualif]
def Le1 (i₀ : Int) (p₁ : Int) : Prop :=
  (i₀ ≤ (p₁ - 1))

end Test01Qualifs

open Test01Qualifs

set_option maxHeartbeats 5000000
def Test01_proof : Test01 := by
  unfold Test01
  try solve_fixpoint

end F
