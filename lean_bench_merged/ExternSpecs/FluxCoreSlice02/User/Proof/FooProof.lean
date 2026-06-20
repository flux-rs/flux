import LeanFixpoint
import ExternSpecs.FluxCoreSlice02.Flux.Prelude
import ExternSpecs.FluxCoreSlice02.Flux.VC.Foo
open Classical
set_option linter.unusedVariables false


namespace F

namespace FooQualifs

@[qualif]
def EqTrue (out₀ : Prop) : Prop :=
  out₀

@[qualif]
def EqFalse (out₀ : Prop) : Prop :=
  (¬out₀)

@[qualif]
def EqZero (out₀ : Int) : Prop :=
  (out₀ = 0)

@[qualif]
def GtZero (out₀ : Int) : Prop :=
  (out₀ > 0)

@[qualif]
def GeZero (out₀ : Int) : Prop :=
  (out₀ ≥ 0)

@[qualif]
def LtZero (out₀ : Int) : Prop :=
  (out₀ < 0)

@[qualif]
def LeZero (out₀ : Int) : Prop :=
  (out₀ ≤ 0)

@[qualif]
def Eq (out₀ : Int) (out₁ : Int) : Prop :=
  (out₀ = out₁)

@[qualif]
def Gt (out₀ : Int) (out₁ : Int) : Prop :=
  (out₀ > out₁)

@[qualif]
def Ge (out₀ : Int) (out₁ : Int) : Prop :=
  (out₀ ≥ out₁)

@[qualif]
def Lt (out₀ : Int) (out₁ : Int) : Prop :=
  (out₀ < out₁)

@[qualif]
def Le (out₀ : Int) (out₁ : Int) : Prop :=
  (out₀ ≤ out₁)

@[qualif]
def Le1 (out₀ : Int) (out₁ : Int) : Prop :=
  (out₀ ≤ (out₁ - 1))

end FooQualifs

open FooQualifs

set_option maxHeartbeats 5000000
#time def Foo_proof : Foo := by
  unfold Foo
  solve_fixpoint_combo

end F
