import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Baz
open Classical

namespace F

namespace BazQualifs

@[qualif]
def EqTrue (x₀ : Prop) : Prop :=
  x₀

@[qualif]
def EqFalse (x₀ : Prop) : Prop :=
  (¬x₀)

@[qualif]
def EqZero (x₀ : Int) : Prop :=
  (x₀ = 0)

@[qualif]
def GtZero (x₀ : Int) : Prop :=
  (x₀ > 0)

@[qualif]
def GeZero (x₀ : Int) : Prop :=
  (x₀ ≥ 0)

@[qualif]
def LtZero (x₀ : Int) : Prop :=
  (x₀ < 0)

@[qualif]
def LeZero (x₀ : Int) : Prop :=
  (x₀ ≤ 0)

@[qualif]
def Eq (x₀ : Int) (v₀ : Int) : Prop :=
  (x₀ = v₀)

@[qualif]
def Gt (x₀ : Int) (v₀ : Int) : Prop :=
  (x₀ > v₀)

@[qualif]
def Ge (x₀ : Int) (v₀ : Int) : Prop :=
  (x₀ ≥ v₀)

@[qualif]
def Lt (x₀ : Int) (v₀ : Int) : Prop :=
  (x₀ < v₀)

@[qualif]
def Le (x₀ : Int) (v₀ : Int) : Prop :=
  (x₀ ≤ v₀)

@[qualif]
def Le1 (x₀ : Int) (v₀ : Int) : Prop :=
  (x₀ ≤ (v₀ - 1))

end BazQualifs

open BazQualifs

set_option maxHeartbeats 5000000
def Baz_proof : Baz := by
  unfold Baz
  try solve_fixpoint

end F
