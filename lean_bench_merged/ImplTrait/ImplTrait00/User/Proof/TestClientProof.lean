import LeanFixpoint
import ImplTrait.ImplTrait00.Flux.Prelude
import ImplTrait.ImplTrait00.Flux.VC.TestClient
open Classical
set_option linter.unusedVariables false


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
#time def TestClient_proof : TestClient := by
  unfold TestClient
  solve_fixpoint_combo

end F
