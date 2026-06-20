import LeanFixpoint
import Surface.Kmeans.Flux.Prelude
import Surface.Kmeans.Flux.VC.Kmeans
open Classical
set_option linter.unusedVariables false


namespace F

namespace KmeansQualifs

@[qualif]
def EqTrue (ps₀ : Prop) : Prop :=
  ps₀

@[qualif]
def EqFalse (ps₀ : Prop) : Prop :=
  (¬ps₀)

@[qualif]
def EqZero (ps₀ : Int) : Prop :=
  (ps₀ = 0)

@[qualif]
def GtZero (ps₀ : Int) : Prop :=
  (ps₀ > 0)

@[qualif]
def GeZero (ps₀ : Int) : Prop :=
  (ps₀ ≥ 0)

@[qualif]
def LtZero (ps₀ : Int) : Prop :=
  (ps₀ < 0)

@[qualif]
def LeZero (ps₀ : Int) : Prop :=
  (ps₀ ≤ 0)

@[qualif]
def Eq (ps₀ : Int) (iters₀ : Int) : Prop :=
  (ps₀ = iters₀)

@[qualif]
def Gt (ps₀ : Int) (iters₀ : Int) : Prop :=
  (ps₀ > iters₀)

@[qualif]
def Ge (ps₀ : Int) (iters₀ : Int) : Prop :=
  (ps₀ ≥ iters₀)

@[qualif]
def Lt (ps₀ : Int) (iters₀ : Int) : Prop :=
  (ps₀ < iters₀)

@[qualif]
def Le (ps₀ : Int) (iters₀ : Int) : Prop :=
  (ps₀ ≤ iters₀)

@[qualif]
def Le1 (ps₀ : Int) (iters₀ : Int) : Prop :=
  (ps₀ ≤ (iters₀ - 1))

end KmeansQualifs

open KmeansQualifs

set_option maxHeartbeats 5000000
#time def Kmeans_proof : Kmeans := by
  unfold Kmeans
  solve_fixpoint_combo

end F
