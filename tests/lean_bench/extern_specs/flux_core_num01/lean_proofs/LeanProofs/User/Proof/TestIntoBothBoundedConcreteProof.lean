import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestIntoBothBoundedConcrete
open Classical
set_option linter.unusedVariables false


namespace F

namespace TestIntoBothBoundedConcreteQualifs

@[qualif]
def EqTrue (r₀ : Prop) : Prop :=
  r₀

@[qualif]
def EqFalse (r₀ : Prop) : Prop :=
  (¬r₀)

@[qualif]
def EqZero (r₀ : Int) : Prop :=
  (r₀ = 0)

@[qualif]
def GtZero (r₀ : Int) : Prop :=
  (r₀ > 0)

@[qualif]
def GeZero (r₀ : Int) : Prop :=
  (r₀ ≥ 0)

@[qualif]
def LtZero (r₀ : Int) : Prop :=
  (r₀ < 0)

@[qualif]
def LeZero (r₀ : Int) : Prop :=
  (r₀ ≤ 0)

@[qualif]
def Eq (r₀ : Int) (v₀ : Int) : Prop :=
  (r₀ = v₀)

@[qualif]
def Gt (r₀ : Int) (v₀ : Int) : Prop :=
  (r₀ > v₀)

@[qualif]
def Ge (r₀ : Int) (v₀ : Int) : Prop :=
  (r₀ ≥ v₀)

@[qualif]
def Lt (r₀ : Int) (v₀ : Int) : Prop :=
  (r₀ < v₀)

@[qualif]
def Le (r₀ : Int) (v₀ : Int) : Prop :=
  (r₀ ≤ v₀)

@[qualif]
def Le1 (r₀ : Int) (v₀ : Int) : Prop :=
  (r₀ ≤ (v₀ - 1))

end TestIntoBothBoundedConcreteQualifs

open TestIntoBothBoundedConcreteQualifs

set_option maxHeartbeats 5000000
def TestIntoBothBoundedConcrete_proof : TestIntoBothBoundedConcrete := by
  unfold TestIntoBothBoundedConcrete
  try rewriteKs
  try fusion
  try solve_fixpoint

end F
