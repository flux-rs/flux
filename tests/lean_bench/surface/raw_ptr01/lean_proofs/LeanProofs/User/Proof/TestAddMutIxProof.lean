import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestAddMutIx
open Classical

namespace F

namespace TestAddMutIxQualifs

@[qualif]
def EqTrue (v₀ : Prop) : Prop :=
  v₀

@[qualif]
def EqFalse (v₀ : Prop) : Prop :=
  (¬v₀)

@[qualif]
def EqZero (v₀ : Int) : Prop :=
  (v₀ = 0)

@[qualif]
def GtZero (v₀ : Int) : Prop :=
  (v₀ > 0)

@[qualif]
def GeZero (v₀ : Int) : Prop :=
  (v₀ ≥ 0)

@[qualif]
def LtZero (v₀ : Int) : Prop :=
  (v₀ < 0)

@[qualif]
def LeZero (v₀ : Int) : Prop :=
  (v₀ ≤ 0)

@[qualif]
def Eq (v₀ : Int) (p₀ : Int) : Prop :=
  (v₀ = p₀)

@[qualif]
def Gt (v₀ : Int) (p₀ : Int) : Prop :=
  (v₀ > p₀)

@[qualif]
def Ge (v₀ : Int) (p₀ : Int) : Prop :=
  (v₀ ≥ p₀)

@[qualif]
def Lt (v₀ : Int) (p₀ : Int) : Prop :=
  (v₀ < p₀)

@[qualif]
def Le (v₀ : Int) (p₀ : Int) : Prop :=
  (v₀ ≤ p₀)

@[qualif]
def Le1 (v₀ : Int) (p₀ : Int) : Prop :=
  (v₀ ≤ (p₀ - 1))

end TestAddMutIxQualifs

open TestAddMutIxQualifs

def TestAddMutIx_proof : TestAddMutIx := by
  unfold TestAddMutIx
  try solve_fixpoint

end F
