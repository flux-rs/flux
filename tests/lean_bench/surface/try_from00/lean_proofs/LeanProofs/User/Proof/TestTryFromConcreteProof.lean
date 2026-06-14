import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestTryFromConcrete
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestTryFromConcreteQualifs

@[qualif]
def EqTrue (v₀ : Prop) : Prop :=
  v₀

@[qualif]
def EqFalse (v₀ : Prop) : Prop :=
  (¬v₀)

@[qualif]
def EqZero (v₀ : Int) : Prop :=
  (v₀ = 0)

@[qualif]
def GtZero (v₀ : Int) : Prop :=
  (v₀ > 0)

@[qualif]
def GeZero (v₀ : Int) : Prop :=
  (v₀ ≥ 0)

@[qualif]
def LtZero (v₀ : Int) : Prop :=
  (v₀ < 0)

@[qualif]
def LeZero (v₀ : Int) : Prop :=
  (v₀ ≤ 0)

@[qualif]
def Eq (v₀ : Int) (m₀ : Int) : Prop :=
  (v₀ = m₀)

@[qualif]
def Gt (v₀ : Int) (m₀ : Int) : Prop :=
  (v₀ > m₀)

@[qualif]
def Ge (v₀ : Int) (m₀ : Int) : Prop :=
  (v₀ ≥ m₀)

@[qualif]
def Lt (v₀ : Int) (m₀ : Int) : Prop :=
  (v₀ < m₀)

@[qualif]
def Le (v₀ : Int) (m₀ : Int) : Prop :=
  (v₀ ≤ m₀)

@[qualif]
def Le1 (v₀ : Int) (m₀ : Int) : Prop :=
  (v₀ ≤ (m₀ - 1))

end TestTryFromConcreteQualifs

open TestTryFromConcreteQualifs

set_option maxHeartbeats 5000000
def TestTryFromConcrete_proof : TestTryFromConcrete := by
  unfold TestTryFromConcrete
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
