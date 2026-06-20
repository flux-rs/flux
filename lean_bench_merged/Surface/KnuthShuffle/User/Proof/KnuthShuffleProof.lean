import LeanFixpoint
import Surface.KnuthShuffle.Flux.Prelude
import Surface.KnuthShuffle.Flux.VC.KnuthShuffle
open Classical
set_option linter.unusedVariables false


namespace F

namespace KnuthShuffleQualifs

@[qualif]
def EqTrue (n₁ : Prop) : Prop :=
  n₁

@[qualif]
def EqFalse (n₁ : Prop) : Prop :=
  (¬n₁)

@[qualif]
def EqZero (n₁ : Int) : Prop :=
  (n₁ = 0)

@[qualif]
def GtZero (n₁ : Int) : Prop :=
  (n₁ > 0)

@[qualif]
def GeZero (n₁ : Int) : Prop :=
  (n₁ ≥ 0)

@[qualif]
def LtZero (n₁ : Int) : Prop :=
  (n₁ < 0)

@[qualif]
def LeZero (n₁ : Int) : Prop :=
  (n₁ ≤ 0)

@[qualif]
def Eq (n₁ : Int) (i₀ : Int) : Prop :=
  (n₁ = i₀)

@[qualif]
def Gt (n₁ : Int) (i₀ : Int) : Prop :=
  (n₁ > i₀)

@[qualif]
def Ge (n₁ : Int) (i₀ : Int) : Prop :=
  (n₁ ≥ i₀)

@[qualif]
def Lt (n₁ : Int) (i₀ : Int) : Prop :=
  (n₁ < i₀)

@[qualif]
def Le (n₁ : Int) (i₀ : Int) : Prop :=
  (n₁ ≤ i₀)

@[qualif]
def Le1 (n₁ : Int) (i₀ : Int) : Prop :=
  (n₁ ≤ (i₀ - 1))

end KnuthShuffleQualifs

open KnuthShuffleQualifs

set_option maxHeartbeats 5000000
#time def KnuthShuffle_proof : KnuthShuffle := by
  unfold KnuthShuffle
  solve_fixpoint_combo

end F
