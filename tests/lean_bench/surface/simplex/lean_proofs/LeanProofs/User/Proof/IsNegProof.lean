import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.IsNeg
open Classical

namespace F

namespace IsNegQualifs

@[qualif]
def EqTrue (j₀ : Prop) : Prop :=
  j₀

@[qualif]
def EqFalse (j₀ : Prop) : Prop :=
  (¬j₀)

@[qualif]
def EqZero (j₀ : Int) : Prop :=
  (j₀ = 0)

@[qualif]
def GtZero (j₀ : Int) : Prop :=
  (j₀ > 0)

@[qualif]
def GeZero (j₀ : Int) : Prop :=
  (j₀ ≥ 0)

@[qualif]
def LtZero (j₀ : Int) : Prop :=
  (j₀ < 0)

@[qualif]
def LeZero (j₀ : Int) : Prop :=
  (j₀ ≤ 0)

@[qualif]
def Eq (j₀ : Int) (a'₁ : Int) : Prop :=
  (j₀ = a'₁)

@[qualif]
def Gt (j₀ : Int) (a'₁ : Int) : Prop :=
  (j₀ > a'₁)

@[qualif]
def Ge (j₀ : Int) (a'₁ : Int) : Prop :=
  (j₀ ≥ a'₁)

@[qualif]
def Lt (j₀ : Int) (a'₁ : Int) : Prop :=
  (j₀ < a'₁)

@[qualif]
def Le (j₀ : Int) (a'₁ : Int) : Prop :=
  (j₀ ≤ a'₁)

@[qualif]
def Le1 (j₀ : Int) (a'₁ : Int) : Prop :=
  (j₀ ≤ (a'₁ - 1))

end IsNegQualifs

open IsNegQualifs

def IsNeg_proof : IsNeg := by
  unfold IsNeg
  try solve_fixpoint

end F
