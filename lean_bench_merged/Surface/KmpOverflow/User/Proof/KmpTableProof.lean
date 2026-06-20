import LeanFixpoint
import Surface.KmpOverflow.Flux.Prelude
import Surface.KmpOverflow.Flux.VC.KmpTable
open Classical
set_option linter.unusedVariables false


namespace F

namespace KmpTableQualifs

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
def Eq (a'₀ : Int) (i₀ : Int) : Prop :=
  (a'₀ = i₀)

@[qualif]
def Gt (a'₀ : Int) (i₀ : Int) : Prop :=
  (a'₀ > i₀)

@[qualif]
def Ge (a'₀ : Int) (i₀ : Int) : Prop :=
  (a'₀ ≥ i₀)

@[qualif]
def Lt (a'₀ : Int) (i₀ : Int) : Prop :=
  (a'₀ < i₀)

@[qualif]
def Le (a'₀ : Int) (i₀ : Int) : Prop :=
  (a'₀ ≤ i₀)

@[qualif]
def Le1 (a'₀ : Int) (i₀ : Int) : Prop :=
  (a'₀ ≤ (i₀ - 1))

end KmpTableQualifs

open KmpTableQualifs

set_option maxHeartbeats 5000000
#time def KmpTable_proof : KmpTable := by
  unfold KmpTable
  solve_fixpoint_combo

end F
