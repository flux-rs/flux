import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Foo
open Classical

namespace F

namespace FooQualifs

@[qualif]
def MyQ1 (a'₄ : Int) (a'₅ : Int) (a'₆ : Int) (a'₇ : Int) : Prop :=
  (((0 ≤ a'₄) ∧ (a'₄ < a'₅)) ∨ ((a'₆ ≤ a'₄) ∧ (a'₄ < a'₇)))

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
def Eq (i₀ : Int) (i₁ : Int) : Prop :=
  (i₀ = i₁)

@[qualif]
def Gt (i₀ : Int) (i₁ : Int) : Prop :=
  (i₀ > i₁)

@[qualif]
def Ge (i₀ : Int) (i₁ : Int) : Prop :=
  (i₀ ≥ i₁)

@[qualif]
def Lt (i₀ : Int) (i₁ : Int) : Prop :=
  (i₀ < i₁)

@[qualif]
def Le (i₀ : Int) (i₁ : Int) : Prop :=
  (i₀ ≤ i₁)

@[qualif]
def Le1 (i₀ : Int) (i₁ : Int) : Prop :=
  (i₀ ≤ (i₁ - 1))

end FooQualifs

open FooQualifs

set_option maxHeartbeats 5000000
def Foo_proof : Foo := by
  unfold Foo
  try solve_fixpoint

end F
