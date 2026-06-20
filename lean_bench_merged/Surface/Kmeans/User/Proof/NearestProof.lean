import LeanFixpoint
import Surface.Kmeans.Flux.Prelude
import Surface.Kmeans.Flux.VC.Nearest
open Classical
set_option linter.unusedVariables false


namespace F

namespace NearestQualifs

@[qualif]
def EqTrue (res₀ : Prop) : Prop :=
  res₀

@[qualif]
def EqFalse (res₀ : Prop) : Prop :=
  (¬res₀)

@[qualif]
def EqZero (res₀ : Int) : Prop :=
  (res₀ = 0)

@[qualif]
def GtZero (res₀ : Int) : Prop :=
  (res₀ > 0)

@[qualif]
def GeZero (res₀ : Int) : Prop :=
  (res₀ ≥ 0)

@[qualif]
def LtZero (res₀ : Int) : Prop :=
  (res₀ < 0)

@[qualif]
def LeZero (res₀ : Int) : Prop :=
  (res₀ ≤ 0)

@[qualif]
def Eq (res₀ : Int) (i₀ : Int) : Prop :=
  (res₀ = i₀)

@[qualif]
def Gt (res₀ : Int) (i₀ : Int) : Prop :=
  (res₀ > i₀)

@[qualif]
def Ge (res₀ : Int) (i₀ : Int) : Prop :=
  (res₀ ≥ i₀)

@[qualif]
def Lt (res₀ : Int) (i₀ : Int) : Prop :=
  (res₀ < i₀)

@[qualif]
def Le (res₀ : Int) (i₀ : Int) : Prop :=
  (res₀ ≤ i₀)

@[qualif]
def Le1 (res₀ : Int) (i₀ : Int) : Prop :=
  (res₀ ≤ (i₀ - 1))

end NearestQualifs

open NearestQualifs

set_option maxHeartbeats 5000000
#time def Nearest_proof : Nearest := by
  unfold Nearest
  solve_fixpoint_combo

end F
