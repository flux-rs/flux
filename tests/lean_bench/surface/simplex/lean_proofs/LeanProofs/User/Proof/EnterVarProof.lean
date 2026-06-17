import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.EnterVar
open Classical
set_option linter.unusedVariables false


namespace F

namespace EnterVarQualifs

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
def Eq (j₀ : Int) (j_₀ : Int) : Prop :=
  (j₀ = j_₀)

@[qualif]
def Gt (j₀ : Int) (j_₀ : Int) : Prop :=
  (j₀ > j_₀)

@[qualif]
def Ge (j₀ : Int) (j_₀ : Int) : Prop :=
  (j₀ ≥ j_₀)

@[qualif]
def Lt (j₀ : Int) (j_₀ : Int) : Prop :=
  (j₀ < j_₀)

@[qualif]
def Le (j₀ : Int) (j_₀ : Int) : Prop :=
  (j₀ ≤ j_₀)

@[qualif]
def Le1 (j₀ : Int) (j_₀ : Int) : Prop :=
  (j₀ ≤ (j_₀ - 1))

end EnterVarQualifs

open EnterVarQualifs

set_option maxHeartbeats 5000000
#time def EnterVar_proof : EnterVar := by
  unfold EnterVar
  solve_fixpoint_combo

end F
