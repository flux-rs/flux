import LeanFixpoint
import Structs.Dot02.Flux.Prelude
import Structs.Dot02.Flux.VC.MkPairsWithBound
open Classical
set_option linter.unusedVariables false


namespace F

namespace MkPairsWithBoundQualifs

@[qualif]
def MyQ1 (a'₅ : Int) (a'₆ : Int) (a'₇ : Int) : Prop :=
  ((a'₅ + a'₆) ≤ (a'₇ + 10))

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

end MkPairsWithBoundQualifs

open MkPairsWithBoundQualifs

set_option maxHeartbeats 5000000
#time def MkPairsWithBound_proof : MkPairsWithBound := by
  unfold MkPairsWithBound
  solve_fixpoint_combo

end F
