import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.OpaqueStruct01
open Classical
set_option linter.unusedVariables false


namespace F

namespace OpaqueStruct01Qualifs

@[qualif]
def EqTrue (p₀ : Prop) : Prop :=
  p₀

@[qualif]
def EqFalse (p₀ : Prop) : Prop :=
  (¬p₀)

@[qualif]
def EqZero (p₀ : Int) : Prop :=
  (p₀ = 0)

@[qualif]
def GtZero (p₀ : Int) : Prop :=
  (p₀ > 0)

@[qualif]
def GeZero (p₀ : Int) : Prop :=
  (p₀ ≥ 0)

@[qualif]
def LtZero (p₀ : Int) : Prop :=
  (p₀ < 0)

@[qualif]
def LeZero (p₀ : Int) : Prop :=
  (p₀ ≤ 0)

@[qualif]
def Eq (p₀ : Int) (b₀ : Int) : Prop :=
  (p₀ = b₀)

@[qualif]
def Gt (p₀ : Int) (b₀ : Int) : Prop :=
  (p₀ > b₀)

@[qualif]
def Ge (p₀ : Int) (b₀ : Int) : Prop :=
  (p₀ ≥ b₀)

@[qualif]
def Lt (p₀ : Int) (b₀ : Int) : Prop :=
  (p₀ < b₀)

@[qualif]
def Le (p₀ : Int) (b₀ : Int) : Prop :=
  (p₀ ≤ b₀)

@[qualif]
def Le1 (p₀ : Int) (b₀ : Int) : Prop :=
  (p₀ ≤ (b₀ - 1))

end OpaqueStruct01Qualifs

open OpaqueStruct01Qualifs

set_option maxHeartbeats 5000000
def OpaqueStruct01_proof : OpaqueStruct01 := by
  unfold OpaqueStruct01
  try solve_fixpoint

end F
