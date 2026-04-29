import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestWithQualifier
open Classical

namespace F

namespace TestWithQualifierQualifs

@[qualif]
def Auto_240_244 (a'₂ : Int) (a'₃ : Int) (a'₄ : Int) : Prop :=
  ((((a'₂ + a'₃) = a'₄) ∧ (a'₃ ≥ (99 - 99))) ∧ (a'₂ ≥ (66 - 66)))

@[qualif]
def EqTrue (res₀ : Prop) : Prop :=
  res₀

@[qualif]
def EqFalse (res₀ : Prop) : Prop :=
  (¬res₀)

@[qualif]
def EqZero (res₀ : Int) : Prop :=
  (res₀ = 0)

@[qualif]
def GtZero (res₀ : Int) : Prop :=
  (res₀ > 0)

@[qualif]
def GeZero (res₀ : Int) : Prop :=
  (res₀ ≥ 0)

@[qualif]
def LtZero (res₀ : Int) : Prop :=
  (res₀ < 0)

@[qualif]
def LeZero (res₀ : Int) : Prop :=
  (res₀ ≤ 0)

@[qualif]
def Eq (res₀ : Int) (i₀ : Int) : Prop :=
  (res₀ = i₀)

@[qualif]
def Gt (res₀ : Int) (i₀ : Int) : Prop :=
  (res₀ > i₀)

@[qualif]
def Ge (res₀ : Int) (i₀ : Int) : Prop :=
  (res₀ ≥ i₀)

@[qualif]
def Lt (res₀ : Int) (i₀ : Int) : Prop :=
  (res₀ < i₀)

@[qualif]
def Le (res₀ : Int) (i₀ : Int) : Prop :=
  (res₀ ≤ i₀)

@[qualif]
def Le1 (res₀ : Int) (i₀ : Int) : Prop :=
  (res₀ ≤ (i₀ - 1))

end TestWithQualifierQualifs

open TestWithQualifierQualifs

def TestWithQualifier_proof : TestWithQualifier := by
  unfold TestWithQualifier
  try solve_fixpoint

end F
