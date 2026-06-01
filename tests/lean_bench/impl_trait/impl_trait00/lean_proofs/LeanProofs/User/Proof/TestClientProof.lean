import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestClient
open Classical

namespace F

namespace TestClientQualifs

@[qualif]
def EqTrue (it₀ : Prop) : Prop :=
  it₀

@[qualif]
def EqFalse (it₀ : Prop) : Prop :=
  (¬it₀)

@[qualif]
def EqZero (it₀ : Int) : Prop :=
  (it₀ = 0)

@[qualif]
def GtZero (it₀ : Int) : Prop :=
  (it₀ > 0)

@[qualif]
def GeZero (it₀ : Int) : Prop :=
  (it₀ ≥ 0)

@[qualif]
def LtZero (it₀ : Int) : Prop :=
  (it₀ < 0)

@[qualif]
def LeZero (it₀ : Int) : Prop :=
  (it₀ ≤ 0)

@[qualif]
def Eq (it₀ : Int) (a'₁ : Int) : Prop :=
  (it₀ = a'₁)

@[qualif]
def Gt (it₀ : Int) (a'₁ : Int) : Prop :=
  (it₀ > a'₁)

@[qualif]
def Ge (it₀ : Int) (a'₁ : Int) : Prop :=
  (it₀ ≥ a'₁)

@[qualif]
def Lt (it₀ : Int) (a'₁ : Int) : Prop :=
  (it₀ < a'₁)

@[qualif]
def Le (it₀ : Int) (a'₁ : Int) : Prop :=
  (it₀ ≤ a'₁)

@[qualif]
def Le1 (it₀ : Int) (a'₁ : Int) : Prop :=
  (it₀ ≤ (a'₁ - 1))

end TestClientQualifs

open TestClientQualifs

set_option maxHeartbeats 5000000
def TestClient_proof : TestClient := by
  unfold TestClient
  try solve_fixpoint

end F
