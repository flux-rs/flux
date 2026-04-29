import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def FirstHalf := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   ∀ (a'₁ : Int),
    (a'₁ ≥ 0) ->
     (∀ (v₀ : Int),
      (v₀ > 0) ->
       ((k0 v₀ a'₀ a'₁))) ∧
     (∀ (a'₃ : Int),
      ∀ (a'₄ : Int),
       (a'₃ ≥ 0) ->
        (a'₄ ≥ 0) ->
         ∀ (a'₅ : Int),
          ((k0 a'₅ a'₀ a'₁)) ->
           (a'₅ ≥ 0))
     
end F
