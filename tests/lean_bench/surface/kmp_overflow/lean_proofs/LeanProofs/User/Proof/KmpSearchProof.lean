import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.KmpSearch
open Classical
set_option linter.unusedVariables false


namespace F

namespace KmpSearchQualifs

@[qualif]
def EqTrue (t_i₀ : Prop) : Prop :=
  t_i₀

@[qualif]
def EqFalse (t_i₀ : Prop) : Prop :=
  (¬t_i₀)

@[qualif]
def EqZero (t_i₀ : Int) : Prop :=
  (t_i₀ = 0)

@[qualif]
def GtZero (t_i₀ : Int) : Prop :=
  (t_i₀ > 0)

@[qualif]
def GeZero (t_i₀ : Int) : Prop :=
  (t_i₀ ≥ 0)

@[qualif]
def LtZero (t_i₀ : Int) : Prop :=
  (t_i₀ < 0)

@[qualif]
def LeZero (t_i₀ : Int) : Prop :=
  (t_i₀ ≤ 0)

@[qualif]
def Eq (t_i₀ : Int) (p_i₀ : Int) : Prop :=
  (t_i₀ = p_i₀)

@[qualif]
def Gt (t_i₀ : Int) (p_i₀ : Int) : Prop :=
  (t_i₀ > p_i₀)

@[qualif]
def Ge (t_i₀ : Int) (p_i₀ : Int) : Prop :=
  (t_i₀ ≥ p_i₀)

@[qualif]
def Lt (t_i₀ : Int) (p_i₀ : Int) : Prop :=
  (t_i₀ < p_i₀)

@[qualif]
def Le (t_i₀ : Int) (p_i₀ : Int) : Prop :=
  (t_i₀ ≤ p_i₀)

@[qualif]
def Le1 (t_i₀ : Int) (p_i₀ : Int) : Prop :=
  (t_i₀ ≤ (p_i₀ - 1))

end KmpSearchQualifs

open KmpSearchQualifs

set_option maxHeartbeats 5000000
def KmpSearch_proof : KmpSearch := by
  unfold KmpSearch
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
