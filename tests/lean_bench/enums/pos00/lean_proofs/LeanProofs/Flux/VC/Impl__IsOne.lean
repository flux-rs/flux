import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Impl__IsOne := 
 ∀ (n₀ : Int),
  (n₀ > 0) ->
   (∀ (n₁ : Int),
    (n₀ = (2 * n₁)) ->
     (n₁ > 0) ->
      (False = (n₀ = 1))) ∧
   (∀ (n₂ : Int),
    (n₀ = ((2 * n₂) + 1)) ->
     (n₂ > 0) ->
      (False = (n₀ = 1)))
   
end F
