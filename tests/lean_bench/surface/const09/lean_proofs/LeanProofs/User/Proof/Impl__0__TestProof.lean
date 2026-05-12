import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__0__Test
open Classical

namespace F

namespace Impl0TestQualifs

@[qualif]
def EqTrue (queue_idx₀ : Prop) : Prop :=
  queue_idx₀

@[qualif]
def EqFalse (queue_idx₀ : Prop) : Prop :=
  (¬queue_idx₀)

@[qualif]
def EqZero (queue_idx₀ : Int) : Prop :=
  (queue_idx₀ = 0)

@[qualif]
def GtZero (queue_idx₀ : Int) : Prop :=
  (queue_idx₀ > 0)

@[qualif]
def GeZero (queue_idx₀ : Int) : Prop :=
  (queue_idx₀ ≥ 0)

@[qualif]
def LtZero (queue_idx₀ : Int) : Prop :=
  (queue_idx₀ < 0)

@[qualif]
def LeZero (queue_idx₀ : Int) : Prop :=
  (queue_idx₀ ≤ 0)

@[qualif]
def Eq (queue_idx₀ : Int) (a'₁ : Int) : Prop :=
  (queue_idx₀ = a'₁)

@[qualif]
def Gt (queue_idx₀ : Int) (a'₁ : Int) : Prop :=
  (queue_idx₀ > a'₁)

@[qualif]
def Ge (queue_idx₀ : Int) (a'₁ : Int) : Prop :=
  (queue_idx₀ ≥ a'₁)

@[qualif]
def Lt (queue_idx₀ : Int) (a'₁ : Int) : Prop :=
  (queue_idx₀ < a'₁)

@[qualif]
def Le (queue_idx₀ : Int) (a'₁ : Int) : Prop :=
  (queue_idx₀ ≤ a'₁)

@[qualif]
def Le1 (queue_idx₀ : Int) (a'₁ : Int) : Prop :=
  (queue_idx₀ ≤ (a'₁ - 1))

end Impl0TestQualifs

open Impl0TestQualifs

def Impl__0__Test_proof : Impl__0__Test := by
  unfold Impl__0__Test
  try solve_fixpoint

end F
