import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Mappend
open Classical
set_option linter.unusedVariables false


namespace F

namespace MappendQualifs

@[qualif]
def EqTrue (n₀ : Prop) : Prop :=
  n₀

@[qualif]
def EqFalse (n₀ : Prop) : Prop :=
  (¬n₀)

@[qualif]
def EqZero (n₀ : Int) : Prop :=
  (n₀ = 0)

@[qualif]
def GtZero (n₀ : Int) : Prop :=
  (n₀ > 0)

@[qualif]
def GeZero (n₀ : Int) : Prop :=
  (n₀ ≥ 0)

@[qualif]
def LtZero (n₀ : Int) : Prop :=
  (n₀ < 0)

@[qualif]
def LeZero (n₀ : Int) : Prop :=
  (n₀ ≤ 0)

@[qualif]
def Eq (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ = a'₁)

@[qualif]
def Gt (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ > a'₁)

@[qualif]
def Ge (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ ≥ a'₁)

@[qualif]
def Lt (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ < a'₁)

@[qualif]
def Le (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ ≤ a'₁)

@[qualif]
def Le1 (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ ≤ (a'₁ - 1))

end MappendQualifs

open MappendQualifs

set_option maxHeartbeats 5000000
def Mappend_proof : Mappend := by
  unfold Mappend
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
