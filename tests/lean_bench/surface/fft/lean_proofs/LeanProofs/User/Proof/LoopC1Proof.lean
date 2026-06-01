import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LoopC1
open Classical

namespace F

namespace LoopC1Qualifs

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
def Eq (j₀ : Int) (v₀ : Int) : Prop :=
  (j₀ = v₀)

@[qualif]
def Gt (j₀ : Int) (v₀ : Int) : Prop :=
  (j₀ > v₀)

@[qualif]
def Ge (j₀ : Int) (v₀ : Int) : Prop :=
  (j₀ ≥ v₀)

@[qualif]
def Lt (j₀ : Int) (v₀ : Int) : Prop :=
  (j₀ < v₀)

@[qualif]
def Le (j₀ : Int) (v₀ : Int) : Prop :=
  (j₀ ≤ v₀)

@[qualif]
def Le1 (j₀ : Int) (v₀ : Int) : Prop :=
  (j₀ ≤ (v₀ - 1))

end LoopC1Qualifs

open LoopC1Qualifs

set_option maxHeartbeats 5000000
def LoopC1_proof : LoopC1 := by
  unfold LoopC1
  try solve_fixpoint

end F
