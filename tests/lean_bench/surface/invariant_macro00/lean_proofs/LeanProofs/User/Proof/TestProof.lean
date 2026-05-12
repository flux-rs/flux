import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test
open Classical

namespace F

namespace TestQualifs

@[qualif]
def Auto_246630_246634 (a'₃ : Int) (a'₄ : Int) (a'₅ : Int) : Prop :=
  ((((a'₃ + a'₄) = a'₅) ∧ (a'₄ ≥ (99 - 99))) ∧ (a'₃ ≥ (66 - 66)))

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

end TestQualifs

open TestQualifs

def Test_proof : Test := by
  unfold Test
  try solve_fixpoint

end F
