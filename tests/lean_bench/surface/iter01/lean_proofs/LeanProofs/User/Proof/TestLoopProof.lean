import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestLoop
open Classical

namespace F

namespace TestLoopQualifs

@[qualif]
def EqTrue (vec₀ : Prop) : Prop :=
  vec₀

@[qualif]
def EqFalse (vec₀ : Prop) : Prop :=
  (¬vec₀)

@[qualif]
def EqZero (vec₀ : Int) : Prop :=
  (vec₀ = 0)

@[qualif]
def GtZero (vec₀ : Int) : Prop :=
  (vec₀ > 0)

@[qualif]
def GeZero (vec₀ : Int) : Prop :=
  (vec₀ ≥ 0)

@[qualif]
def LtZero (vec₀ : Int) : Prop :=
  (vec₀ < 0)

@[qualif]
def LeZero (vec₀ : Int) : Prop :=
  (vec₀ ≤ 0)

@[qualif]
def Eq (vec₀ : Int) (v₀ : Int) : Prop :=
  (vec₀ = v₀)

@[qualif]
def Gt (vec₀ : Int) (v₀ : Int) : Prop :=
  (vec₀ > v₀)

@[qualif]
def Ge (vec₀ : Int) (v₀ : Int) : Prop :=
  (vec₀ ≥ v₀)

@[qualif]
def Lt (vec₀ : Int) (v₀ : Int) : Prop :=
  (vec₀ < v₀)

@[qualif]
def Le (vec₀ : Int) (v₀ : Int) : Prop :=
  (vec₀ ≤ v₀)

@[qualif]
def Le1 (vec₀ : Int) (v₀ : Int) : Prop :=
  (vec₀ ≤ (v₀ - 1))

end TestLoopQualifs

open TestLoopQualifs

def TestLoop_proof : TestLoop := by
  unfold TestLoop
  try solve_fixpoint

end F
