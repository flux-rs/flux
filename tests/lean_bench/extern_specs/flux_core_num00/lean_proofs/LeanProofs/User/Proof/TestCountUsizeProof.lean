import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestCountUsize
open Classical

namespace F

namespace TestCountUsizeQualifs

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

end TestCountUsizeQualifs

open TestCountUsizeQualifs

def TestCountUsize_proof : TestCountUsize := by
  unfold TestCountUsize
  try solve_fixpoint

end F
