import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__0__LenConstMemory
open Classical
set_option linter.unusedVariables false


namespace F

namespace Impl0LenConstMemoryQualifs

@[qualif]
def Sub2 (a'₄ : Int) (a'₅ : Int) (a'₆ : Int) : Prop :=
  (a'₄ = (a'₅ - a'₆))

@[qualif]
def EqTrue (len₀ : Prop) : Prop :=
  len₀

@[qualif]
def EqFalse (len₀ : Prop) : Prop :=
  (¬len₀)

@[qualif]
def EqZero (len₀ : Int) : Prop :=
  (len₀ = 0)

@[qualif]
def GtZero (len₀ : Int) : Prop :=
  (len₀ > 0)

@[qualif]
def GeZero (len₀ : Int) : Prop :=
  (len₀ ≥ 0)

@[qualif]
def LtZero (len₀ : Int) : Prop :=
  (len₀ < 0)

@[qualif]
def LeZero (len₀ : Int) : Prop :=
  (len₀ ≤ 0)

@[qualif]
def Eq (len₀ : Int) (cur₀ : Int) : Prop :=
  (len₀ = cur₀)

@[qualif]
def Gt (len₀ : Int) (cur₀ : Int) : Prop :=
  (len₀ > cur₀)

@[qualif]
def Ge (len₀ : Int) (cur₀ : Int) : Prop :=
  (len₀ ≥ cur₀)

@[qualif]
def Lt (len₀ : Int) (cur₀ : Int) : Prop :=
  (len₀ < cur₀)

@[qualif]
def Le (len₀ : Int) (cur₀ : Int) : Prop :=
  (len₀ ≤ cur₀)

@[qualif]
def Le1 (len₀ : Int) (cur₀ : Int) : Prop :=
  (len₀ ≤ (cur₀ - 1))

end Impl0LenConstMemoryQualifs

open Impl0LenConstMemoryQualifs

set_option maxHeartbeats 5000000
def Impl__0__LenConstMemory_proof : Impl__0__LenConstMemory := by
  unfold Impl__0__LenConstMemory
  solve_fixpoint_combo

end F
