import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test01 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (v₀ : Int),
  (v₀ > 0) ->
   (((k0 v₀ v₀))) ∧
   (∀ (a'₁ : Int),
    ((k0 a'₁ v₀)) ->
     ((a'₁ > 0)) ∧
     (∀ (v₁ : Int),
      (v₁ > 0) ->
       ((k0 v₁ v₀)))
     )
   
end F
