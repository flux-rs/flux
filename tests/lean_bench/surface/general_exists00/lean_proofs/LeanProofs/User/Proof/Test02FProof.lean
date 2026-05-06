import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test02F
open Classical

namespace F

namespace Test02FQualifs

@[qualif]
def EqTrue (a₀ : Prop) : Prop :=
  a₀

@[qualif]
def EqFalse (a₀ : Prop) : Prop :=
  (¬a₀)

@[qualif]
def EqZero (a₀ : Int) : Prop :=
  (a₀ = 0)

@[qualif]
def GtZero (a₀ : Int) : Prop :=
  (a₀ > 0)

@[qualif]
def GeZero (a₀ : Int) : Prop :=
  (a₀ ≥ 0)

@[qualif]
def LtZero (a₀ : Int) : Prop :=
  (a₀ < 0)

@[qualif]
def LeZero (a₀ : Int) : Prop :=
  (a₀ ≤ 0)

@[qualif]
def Eq (a₀ : Int) (a'₁ : Int) : Prop :=
  (a₀ = a'₁)

@[qualif]
def Gt (a₀ : Int) (a'₁ : Int) : Prop :=
  (a₀ > a'₁)

@[qualif]
def Ge (a₀ : Int) (a'₁ : Int) : Prop :=
  (a₀ ≥ a'₁)

@[qualif]
def Lt (a₀ : Int) (a'₁ : Int) : Prop :=
  (a₀ < a'₁)

@[qualif]
def Le (a₀ : Int) (a'₁ : Int) : Prop :=
  (a₀ ≤ a'₁)

@[qualif]
def Le1 (a₀ : Int) (a'₁ : Int) : Prop :=
  (a₀ ≤ (a'₁ - 1))

end Test02FQualifs

open Test02FQualifs

def Test02F_proof : Test02F := by
  unfold Test02F
  try solve_fixpoint

end F
