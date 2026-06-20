import LeanFixpoint
import Surface.Binop.Flux.Prelude
import Surface.Binop.Flux.VC.BitwiseShrU32U32
open Classical
set_option linter.unusedVariables false


namespace F

namespace BitwiseShrU32U32Qualifs

@[qualif]
def EqTrue (a'₀ : Prop) : Prop :=
  a'₀

@[qualif]
def EqFalse (a'₀ : Prop) : Prop :=
  (¬a'₀)

@[qualif]
def EqZero (a'₀ : Int) : Prop :=
  (a'₀ = 0)

@[qualif]
def GtZero (a'₀ : Int) : Prop :=
  (a'₀ > 0)

@[qualif]
def GeZero (a'₀ : Int) : Prop :=
  (a'₀ ≥ 0)

@[qualif]
def LtZero (a'₀ : Int) : Prop :=
  (a'₀ < 0)

@[qualif]
def LeZero (a'₀ : Int) : Prop :=
  (a'₀ ≤ 0)

@[qualif]
def Eq (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ = a'₁)

@[qualif]
def Gt (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ > a'₁)

@[qualif]
def Ge (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ ≥ a'₁)

@[qualif]
def Lt (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ < a'₁)

@[qualif]
def Le (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ ≤ a'₁)

@[qualif]
def Le1 (a'₀ : Int) (a'₁ : Int) : Prop :=
  (a'₀ ≤ (a'₁ - 1))

end BitwiseShrU32U32Qualifs

open BitwiseShrU32U32Qualifs

set_option maxHeartbeats 5000000
#time def BitwiseShrU32U32_proof : BitwiseShrU32U32 := by
  unfold BitwiseShrU32U32
  solve_fixpoint_combo

end F
