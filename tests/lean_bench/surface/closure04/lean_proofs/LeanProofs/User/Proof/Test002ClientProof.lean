import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test002Client
open Classical
set_option linter.unusedVariables false


namespace F

namespace Test002ClientQualifs

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
def Eq (a'₀ : Int) (v₀ : Int) : Prop :=
  (a'₀ = v₀)

@[qualif]
def Gt (a'₀ : Int) (v₀ : Int) : Prop :=
  (a'₀ > v₀)

@[qualif]
def Ge (a'₀ : Int) (v₀ : Int) : Prop :=
  (a'₀ ≥ v₀)

@[qualif]
def Lt (a'₀ : Int) (v₀ : Int) : Prop :=
  (a'₀ < v₀)

@[qualif]
def Le (a'₀ : Int) (v₀ : Int) : Prop :=
  (a'₀ ≤ v₀)

@[qualif]
def Le1 (a'₀ : Int) (v₀ : Int) : Prop :=
  (a'₀ ≤ (v₀ - 1))

end Test002ClientQualifs

open Test002ClientQualifs

set_option maxHeartbeats 5000000
#time def Test002Client_proof : Test002Client := by
  unfold Test002Client
  solve_fixpoint_combo

end F
