import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Client0
open Classical
set_option linter.unusedVariables false


namespace F

namespace Client0Qualifs

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
def Eq (a'₀ : Int) (king₀ : Int) : Prop :=
  (a'₀ = king₀)

@[qualif]
def Gt (a'₀ : Int) (king₀ : Int) : Prop :=
  (a'₀ > king₀)

@[qualif]
def Ge (a'₀ : Int) (king₀ : Int) : Prop :=
  (a'₀ ≥ king₀)

@[qualif]
def Lt (a'₀ : Int) (king₀ : Int) : Prop :=
  (a'₀ < king₀)

@[qualif]
def Le (a'₀ : Int) (king₀ : Int) : Prop :=
  (a'₀ ≤ king₀)

@[qualif]
def Le1 (a'₀ : Int) (king₀ : Int) : Prop :=
  (a'₀ ≤ (king₀ - 1))

end Client0Qualifs

open Client0Qualifs

set_option maxHeartbeats 5000000
def Client0_proof : Client0 := by
  unfold Client0
  solve_fixpoint_combo

end F
