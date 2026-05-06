import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.ApplyClosureToAnimal
open Classical

namespace F

namespace ApplyClosureToAnimalQualifs

@[qualif]
def EqTrue (closure₀ : Prop) : Prop :=
  closure₀

@[qualif]
def EqFalse (closure₀ : Prop) : Prop :=
  (¬closure₀)

@[qualif]
def EqZero (closure₀ : Int) : Prop :=
  (closure₀ = 0)

@[qualif]
def GtZero (closure₀ : Int) : Prop :=
  (closure₀ > 0)

@[qualif]
def GeZero (closure₀ : Int) : Prop :=
  (closure₀ ≥ 0)

@[qualif]
def LtZero (closure₀ : Int) : Prop :=
  (closure₀ < 0)

@[qualif]
def LeZero (closure₀ : Int) : Prop :=
  (closure₀ ≤ 0)

@[qualif]
def Eq (closure₀ : Int) (a'₁ : Int) : Prop :=
  (closure₀ = a'₁)

@[qualif]
def Gt (closure₀ : Int) (a'₁ : Int) : Prop :=
  (closure₀ > a'₁)

@[qualif]
def Ge (closure₀ : Int) (a'₁ : Int) : Prop :=
  (closure₀ ≥ a'₁)

@[qualif]
def Lt (closure₀ : Int) (a'₁ : Int) : Prop :=
  (closure₀ < a'₁)

@[qualif]
def Le (closure₀ : Int) (a'₁ : Int) : Prop :=
  (closure₀ ≤ a'₁)

@[qualif]
def Le1 (closure₀ : Int) (a'₁ : Int) : Prop :=
  (closure₀ ≤ (a'₁ - 1))

end ApplyClosureToAnimalQualifs

open ApplyClosureToAnimalQualifs

def ApplyClosureToAnimal_proof : ApplyClosureToAnimal := by
  unfold ApplyClosureToAnimal
  try solve_fixpoint

end F
