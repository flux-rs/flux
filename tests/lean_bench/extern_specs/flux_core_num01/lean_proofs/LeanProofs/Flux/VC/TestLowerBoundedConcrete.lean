import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestLowerBoundedConcrete := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 100) ->
   ((k0 a'₀))) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (a'₁ ≥ 0) ->
    ((a'₁ = 100) = True))
 
end F
