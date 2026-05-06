import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestAddMutEx := 
 ∀ (v₀ : Int),
  ((c0 v₀) > 1) ->
   ∀ (p₀ : Int),
    ((c0 p₀) = ((c0 v₀) - 0)) ->
     (((c0 p₀) > 0)) ∧
     (∀ (p₁ : Int),
      ((c0 p₁) = ((c0 v₀) - 1)) ->
       ((c0 p₁) > 0))
     
end F
