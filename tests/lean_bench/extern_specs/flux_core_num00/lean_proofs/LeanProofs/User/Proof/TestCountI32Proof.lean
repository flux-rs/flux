import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestCountI32
open Classical

namespace F

namespace TestCountI32Qualifs

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

end TestCountI32Qualifs

open TestCountI32Qualifs

def TestCountI32_proof : TestCountI32 := by
  unfold TestCountI32
  try solve_fixpoint

end F
