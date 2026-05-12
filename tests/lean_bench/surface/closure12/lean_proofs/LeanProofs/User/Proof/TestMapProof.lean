import LeanFixpoint
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.TestMap
open Classical

namespace F

namespace TestMapQualifs

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
def Eq (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ = item₀)

@[qualif]
def Gt (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ > item₀)

@[qualif]
def Ge (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ ≥ item₀)

@[qualif]
def Lt (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ < item₀)

@[qualif]
def Le (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ ≤ item₀)

@[qualif]
def Le1 (a'₀ : Int) (item₀ : Int) : Prop :=
  (a'₀ ≤ (item₀ - 1))

end TestMapQualifs

open TestMapQualifs

def TestMap_proof : TestMap := by
  unfold TestMap
  try solve_fixpoint

end F
