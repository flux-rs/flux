import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.WriteIxI32
open Classical

namespace F

namespace WriteIxI32Qualifs

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
def Eq (v₀ : Int) (value₀ : Int) : Prop :=
  (v₀ = value₀)

@[qualif]
def Gt (v₀ : Int) (value₀ : Int) : Prop :=
  (v₀ > value₀)

@[qualif]
def Ge (v₀ : Int) (value₀ : Int) : Prop :=
  (v₀ ≥ value₀)

@[qualif]
def Lt (v₀ : Int) (value₀ : Int) : Prop :=
  (v₀ < value₀)

@[qualif]
def Le (v₀ : Int) (value₀ : Int) : Prop :=
  (v₀ ≤ value₀)

@[qualif]
def Le1 (v₀ : Int) (value₀ : Int) : Prop :=
  (v₀ ≤ (value₀ - 1))

end WriteIxI32Qualifs

open WriteIxI32Qualifs

set_option maxHeartbeats 5000000
def WriteIxI32_proof : WriteIxI32 := by
  unfold WriteIxI32
  try solve_fixpoint

end F
