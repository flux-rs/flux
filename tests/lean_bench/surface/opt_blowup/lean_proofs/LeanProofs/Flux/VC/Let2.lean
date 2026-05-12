import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Let2 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (a'₀ : Int),
   (n₀ < a'₀) ->
    ∀ (a'₁ : Int),
     (a'₀ < a'₁) ->
      (((k0 a'₁ n₀ a'₀ a'₁))) ∧
      (∀ (a'₂ : Int),
       ((k0 a'₂ n₀ a'₀ a'₁)) ->
        (n₀ < a'₂))
      
end F
