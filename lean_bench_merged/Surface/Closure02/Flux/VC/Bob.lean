import Surface.Closure02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Bob := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (v₀ : Int),
  (0 < v₀) ->
   (0 ≤ v₀) ->
    (∀ (v₁ : Int),
     (10 ≤ v₁) ->
      ((k0 v₁ v₀))) ∧
    (∀ (a'₂ : Int),
     ((k0 a'₂ v₀)) ->
      (10 ≤ a'₂))
    
end F
