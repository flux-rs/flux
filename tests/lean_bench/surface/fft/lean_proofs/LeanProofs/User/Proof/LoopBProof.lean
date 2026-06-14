import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LoopB
open Classical
set_option linter.unusedVariables false


namespace F

namespace LoopBQualifs

@[qualif]
def EqTrue (is₀ : Prop) : Prop :=
  is₀

@[qualif]
def EqFalse (is₀ : Prop) : Prop :=
  (¬is₀)

@[qualif]
def EqZero (is₀ : Int) : Prop :=
  (is₀ = 0)

@[qualif]
def GtZero (is₀ : Int) : Prop :=
  (is₀ > 0)

@[qualif]
def GeZero (is₀ : Int) : Prop :=
  (is₀ ≥ 0)

@[qualif]
def LtZero (is₀ : Int) : Prop :=
  (is₀ < 0)

@[qualif]
def LeZero (is₀ : Int) : Prop :=
  (is₀ ≤ 0)

@[qualif]
def Eq (is₀ : Int) (id₀ : Int) : Prop :=
  (is₀ = id₀)

@[qualif]
def Gt (is₀ : Int) (id₀ : Int) : Prop :=
  (is₀ > id₀)

@[qualif]
def Ge (is₀ : Int) (id₀ : Int) : Prop :=
  (is₀ ≥ id₀)

@[qualif]
def Lt (is₀ : Int) (id₀ : Int) : Prop :=
  (is₀ < id₀)

@[qualif]
def Le (is₀ : Int) (id₀ : Int) : Prop :=
  (is₀ ≤ id₀)

@[qualif]
def Le1 (is₀ : Int) (id₀ : Int) : Prop :=
  (is₀ ≤ (id₀ - 1))

end LoopBQualifs

open LoopBQualifs

set_option maxHeartbeats 5000000
def LoopB_proof : LoopB := by
  unfold LoopB
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
