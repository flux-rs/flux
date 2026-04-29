import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test32
open Classical

namespace F

namespace Test32Qualifs

@[qualif]
def EqTrue (nanos₀ : Prop) : Prop :=
  nanos₀

@[qualif]
def EqFalse (nanos₀ : Prop) : Prop :=
  (¬nanos₀)

@[qualif]
def EqZero (nanos₀ : Int) : Prop :=
  (nanos₀ = 0)

@[qualif]
def GtZero (nanos₀ : Int) : Prop :=
  (nanos₀ > 0)

@[qualif]
def GeZero (nanos₀ : Int) : Prop :=
  (nanos₀ ≥ 0)

@[qualif]
def LtZero (nanos₀ : Int) : Prop :=
  (nanos₀ < 0)

@[qualif]
def LeZero (nanos₀ : Int) : Prop :=
  (nanos₀ ≤ 0)

@[qualif]
def Eq (nanos₀ : Int) (a'₁ : Int) : Prop :=
  (nanos₀ = a'₁)

@[qualif]
def Gt (nanos₀ : Int) (a'₁ : Int) : Prop :=
  (nanos₀ > a'₁)

@[qualif]
def Ge (nanos₀ : Int) (a'₁ : Int) : Prop :=
  (nanos₀ ≥ a'₁)

@[qualif]
def Lt (nanos₀ : Int) (a'₁ : Int) : Prop :=
  (nanos₀ < a'₁)

@[qualif]
def Le (nanos₀ : Int) (a'₁ : Int) : Prop :=
  (nanos₀ ≤ a'₁)

@[qualif]
def Le1 (nanos₀ : Int) (a'₁ : Int) : Prop :=
  (nanos₀ ≤ (a'₁ - 1))

end Test32Qualifs

open Test32Qualifs

def Test32_proof : Test32 := by
  unfold Test32
  try solve_fixpoint

end F
