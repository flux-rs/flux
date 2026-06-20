import LeanFixpoint
import Surface.Bitvec01.Flux.Prelude
import Surface.Bitvec01.Flux.VC.WrapIndex
open Classical
set_option linter.unusedVariables false


namespace F

namespace WrapIndexQualifs

@[qualif]
def EqTrue (index₀ : Prop) : Prop :=
  index₀

@[qualif]
def EqFalse (index₀ : Prop) : Prop :=
  (¬index₀)

@[qualif]
def EqZero (index₀ : Int) : Prop :=
  (index₀ = 0)

@[qualif]
def GtZero (index₀ : Int) : Prop :=
  (index₀ > 0)

@[qualif]
def GeZero (index₀ : Int) : Prop :=
  (index₀ ≥ 0)

@[qualif]
def LtZero (index₀ : Int) : Prop :=
  (index₀ < 0)

@[qualif]
def LeZero (index₀ : Int) : Prop :=
  (index₀ ≤ 0)

@[qualif]
def Eq (index₀ : Int) (a'₁ : Int) : Prop :=
  (index₀ = a'₁)

@[qualif]
def Gt (index₀ : Int) (a'₁ : Int) : Prop :=
  (index₀ > a'₁)

@[qualif]
def Ge (index₀ : Int) (a'₁ : Int) : Prop :=
  (index₀ ≥ a'₁)

@[qualif]
def Lt (index₀ : Int) (a'₁ : Int) : Prop :=
  (index₀ < a'₁)

@[qualif]
def Le (index₀ : Int) (a'₁ : Int) : Prop :=
  (index₀ ≤ a'₁)

@[qualif]
def Le1 (index₀ : Int) (a'₁ : Int) : Prop :=
  (index₀ ≤ (a'₁ - 1))

end WrapIndexQualifs

open WrapIndexQualifs

set_option maxHeartbeats 5000000
#time def WrapIndex_proof : WrapIndex := by
  unfold WrapIndex
  solve_fixpoint_combo

end F
