import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__0__LenConstMemory
open Classical

namespace F

namespace Impl0LenConstMemoryQualifs

@[qualif]
def Sub2 (a'₄ : Int) (a'₅ : Int) (a'₆ : Int) : Prop :=
  (a'₄ = (a'₅ - a'₆))

@[qualif]
def EqTrue (cur₀ : Prop) : Prop :=
  cur₀

@[qualif]
def EqFalse (cur₀ : Prop) : Prop :=
  (¬cur₀)

@[qualif]
def EqZero (cur₀ : Int) : Prop :=
  (cur₀ = 0)

@[qualif]
def GtZero (cur₀ : Int) : Prop :=
  (cur₀ > 0)

@[qualif]
def GeZero (cur₀ : Int) : Prop :=
  (cur₀ ≥ 0)

@[qualif]
def LtZero (cur₀ : Int) : Prop :=
  (cur₀ < 0)

@[qualif]
def LeZero (cur₀ : Int) : Prop :=
  (cur₀ ≤ 0)

@[qualif]
def Eq (cur₀ : Int) (len₀ : Int) : Prop :=
  (cur₀ = len₀)

@[qualif]
def Gt (cur₀ : Int) (len₀ : Int) : Prop :=
  (cur₀ > len₀)

@[qualif]
def Ge (cur₀ : Int) (len₀ : Int) : Prop :=
  (cur₀ ≥ len₀)

@[qualif]
def Lt (cur₀ : Int) (len₀ : Int) : Prop :=
  (cur₀ < len₀)

@[qualif]
def Le (cur₀ : Int) (len₀ : Int) : Prop :=
  (cur₀ ≤ len₀)

@[qualif]
def Le1 (cur₀ : Int) (len₀ : Int) : Prop :=
  (cur₀ ≤ (len₀ - 1))

end Impl0LenConstMemoryQualifs

open Impl0LenConstMemoryQualifs

set_option maxHeartbeats 5000000
def Impl__0__LenConstMemory_proof : Impl__0__LenConstMemory := by
  unfold Impl__0__LenConstMemory
  try solve_fixpoint

end F
