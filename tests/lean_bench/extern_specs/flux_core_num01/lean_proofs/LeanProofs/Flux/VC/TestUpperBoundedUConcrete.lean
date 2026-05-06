import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#8}MAX
import LeanFixpoint
open Classical

namespace F



def TestUpperBoundedUConcrete := ∃ k0 : (a0 : Int) -> Prop, 
 (((1000 ≤ num_{impl#8}_MAX) = True)) ∧
 (∀ (a'₀ : Int),
  (a'₀ = 1000) ->
   ((k0 a'₀))) ∧
 (((1000 ≤ num_{impl#8}_MAX) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (a'₁ ≥ 0) ->
    (((a'₁ = 1000) = True)) ∧
    (((¬((4294967295 + 1) ≤ num_{impl#8}_MAX)) = True))
    )
 
end F
