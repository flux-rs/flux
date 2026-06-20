import LeanFixpoint
import Structs.OpaqueRange.Flux.Prelude
import Structs.OpaqueRange.Flux.VC.Test
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestQualifs

@[qualif]
def EqTrue (r₀ : Prop) : Prop :=
  r₀

@[qualif]
def EqFalse (r₀ : Prop) : Prop :=
  (¬r₀)

@[qualif]
def EqZero (r₀ : Int) : Prop :=
  (r₀ = 0)

@[qualif]
def GtZero (r₀ : Int) : Prop :=
  (r₀ > 0)

@[qualif]
def GeZero (r₀ : Int) : Prop :=
  (r₀ ≥ 0)

@[qualif]
def LtZero (r₀ : Int) : Prop :=
  (r₀ < 0)

@[qualif]
def LeZero (r₀ : Int) : Prop :=
  (r₀ ≤ 0)

@[qualif]
def Eq (r₀ : Int) (a'₁ : Int) : Prop :=
  (r₀ = a'₁)

@[qualif]
def Gt (r₀ : Int) (a'₁ : Int) : Prop :=
  (r₀ > a'₁)

@[qualif]
def Ge (r₀ : Int) (a'₁ : Int) : Prop :=
  (r₀ ≥ a'₁)

@[qualif]
def Lt (r₀ : Int) (a'₁ : Int) : Prop :=
  (r₀ < a'₁)

@[qualif]
def Le (r₀ : Int) (a'₁ : Int) : Prop :=
  (r₀ ≤ a'₁)

@[qualif]
def Le1 (r₀ : Int) (a'₁ : Int) : Prop :=
  (r₀ ≤ (a'₁ - 1))

end TestQualifs

open TestQualifs

set_option maxHeartbeats 5000000
#time def Test_proof : Test := by
  unfold Test
  solve_fixpoint_combo

end F
