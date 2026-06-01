import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__1__Pop
open Classical

namespace F

namespace Impl1PopQualifs

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
def Eq (a'₀ : Int) (n₁ : Int) : Prop :=
  (a'₀ = n₁)

@[qualif]
def Gt (a'₀ : Int) (n₁ : Int) : Prop :=
  (a'₀ > n₁)

@[qualif]
def Ge (a'₀ : Int) (n₁ : Int) : Prop :=
  (a'₀ ≥ n₁)

@[qualif]
def Lt (a'₀ : Int) (n₁ : Int) : Prop :=
  (a'₀ < n₁)

@[qualif]
def Le (a'₀ : Int) (n₁ : Int) : Prop :=
  (a'₀ ≤ n₁)

@[qualif]
def Le1 (a'₀ : Int) (n₁ : Int) : Prop :=
  (a'₀ ≤ (n₁ - 1))

end Impl1PopQualifs

open Impl1PopQualifs

set_option maxHeartbeats 5000000
def Impl__1__Pop_proof : Impl__1__Pop := by
  unfold Impl__1__Pop
  try solve_fixpoint

end F
