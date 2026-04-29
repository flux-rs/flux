import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def RangeImpl__Next := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (lo₀ : Int),
  ∀ (hi₀ : Int),
   ∀ (v₀ : Int),
    ((lo₀ ≤ v₀) ∧ (v₀ ≤ hi₀)) ->
     (v₀ < hi₀) ->
      (((lo₀ ≤ (v₀ + 1))) ∧
      (((v₀ + 1) ≤ hi₀))
      ) ∧
      (((k0 v₀ lo₀ hi₀ v₀))) ∧
      (∀ (a'₁ : Int),
       ((k0 a'₁ lo₀ hi₀ v₀)) ->
        ((lo₀ ≤ a'₁)) ∧
        ((a'₁ < hi₀))
        )
      
end F
