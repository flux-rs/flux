import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestSelect
open Classical

namespace F

namespace TestSelectQualifs

@[qualif]
def EqTrue (guess₀ : Prop) : Prop :=
  guess₀

@[qualif]
def EqFalse (guess₀ : Prop) : Prop :=
  (¬guess₀)

@[qualif]
def EqZero (guess₀ : Int) : Prop :=
  (guess₀ = 0)

@[qualif]
def GtZero (guess₀ : Int) : Prop :=
  (guess₀ > 0)

@[qualif]
def GeZero (guess₀ : Int) : Prop :=
  (guess₀ ≥ 0)

@[qualif]
def LtZero (guess₀ : Int) : Prop :=
  (guess₀ < 0)

@[qualif]
def LeZero (guess₀ : Int) : Prop :=
  (guess₀ ≤ 0)

@[qualif]
def Eq (guess₀ : Int) (secret₀ : Int) : Prop :=
  (guess₀ = secret₀)

@[qualif]
def Gt (guess₀ : Int) (secret₀ : Int) : Prop :=
  (guess₀ > secret₀)

@[qualif]
def Ge (guess₀ : Int) (secret₀ : Int) : Prop :=
  (guess₀ ≥ secret₀)

@[qualif]
def Lt (guess₀ : Int) (secret₀ : Int) : Prop :=
  (guess₀ < secret₀)

@[qualif]
def Le (guess₀ : Int) (secret₀ : Int) : Prop :=
  (guess₀ ≤ secret₀)

@[qualif]
def Le1 (guess₀ : Int) (secret₀ : Int) : Prop :=
  (guess₀ ≤ (secret₀ - 1))

end TestSelectQualifs

open TestSelectQualifs

set_option maxHeartbeats 5000000
def TestSelect_proof : TestSelect := by
  unfold TestSelect
  try solve_fixpoint

end F
