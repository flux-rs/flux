import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.AssertTerminatorTest
open Classical

namespace F

namespace AssertTerminatorTestQualifs

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
def Eq (v₀ : Int) (a₀ : Int) : Prop :=
  (v₀ = a₀)

@[qualif]
def Gt (v₀ : Int) (a₀ : Int) : Prop :=
  (v₀ > a₀)

@[qualif]
def Ge (v₀ : Int) (a₀ : Int) : Prop :=
  (v₀ ≥ a₀)

@[qualif]
def Lt (v₀ : Int) (a₀ : Int) : Prop :=
  (v₀ < a₀)

@[qualif]
def Le (v₀ : Int) (a₀ : Int) : Prop :=
  (v₀ ≤ a₀)

@[qualif]
def Le1 (v₀ : Int) (a₀ : Int) : Prop :=
  (v₀ ≤ (a₀ - 1))

end AssertTerminatorTestQualifs

open AssertTerminatorTestQualifs

set_option maxHeartbeats 5000000
def AssertTerminatorTest_proof : AssertTerminatorTest := by
  unfold AssertTerminatorTest
  try solve_fixpoint

end F
