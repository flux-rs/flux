import LeanFixpoint
import Surface.FibLoop.Flux.Prelude
import Surface.FibLoop.Flux.VC.FibLoop
open Classical
set_option linter.unusedVariables false


namespace F

namespace FibLoopQualifs

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
def Eq (v₀ : Int) (k₀ : Int) : Prop :=
  (v₀ = k₀)

@[qualif]
def Gt (v₀ : Int) (k₀ : Int) : Prop :=
  (v₀ > k₀)

@[qualif]
def Ge (v₀ : Int) (k₀ : Int) : Prop :=
  (v₀ ≥ k₀)

@[qualif]
def Lt (v₀ : Int) (k₀ : Int) : Prop :=
  (v₀ < k₀)

@[qualif]
def Le (v₀ : Int) (k₀ : Int) : Prop :=
  (v₀ ≤ k₀)

@[qualif]
def Le1 (v₀ : Int) (k₀ : Int) : Prop :=
  (v₀ ≤ (k₀ - 1))

end FibLoopQualifs

open FibLoopQualifs

set_option maxHeartbeats 5000000
#time def FibLoop_proof : FibLoop := by
  unfold FibLoop
  solve_fixpoint_combo

end F
