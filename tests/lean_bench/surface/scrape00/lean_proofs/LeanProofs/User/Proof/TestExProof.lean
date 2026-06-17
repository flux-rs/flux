import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestEx
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestExQualifs

@[qualif]
def EqTrue (i₀ : Prop) : Prop :=
  i₀

@[qualif]
def EqFalse (i₀ : Prop) : Prop :=
  (¬i₀)

@[qualif]
def EqZero (i₀ : Int) : Prop :=
  (i₀ = 0)

@[qualif]
def GtZero (i₀ : Int) : Prop :=
  (i₀ > 0)

@[qualif]
def GeZero (i₀ : Int) : Prop :=
  (i₀ ≥ 0)

@[qualif]
def LtZero (i₀ : Int) : Prop :=
  (i₀ < 0)

@[qualif]
def LeZero (i₀ : Int) : Prop :=
  (i₀ ≤ 0)

@[qualif]
def Eq (i₀ : Int) (res₀ : Int) : Prop :=
  (i₀ = res₀)

@[qualif]
def Gt (i₀ : Int) (res₀ : Int) : Prop :=
  (i₀ > res₀)

@[qualif]
def Ge (i₀ : Int) (res₀ : Int) : Prop :=
  (i₀ ≥ res₀)

@[qualif]
def Lt (i₀ : Int) (res₀ : Int) : Prop :=
  (i₀ < res₀)

@[qualif]
def Le (i₀ : Int) (res₀ : Int) : Prop :=
  (i₀ ≤ res₀)

@[qualif]
def Le1 (i₀ : Int) (res₀ : Int) : Prop :=
  (i₀ ≤ (res₀ - 1))

end TestExQualifs

open TestExQualifs

set_option maxHeartbeats 5000000
#time def TestEx_proof : TestEx := by
  unfold TestEx
  solve_fixpoint_combo

end F
