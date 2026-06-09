import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def First := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (∀ (v₀ : Int),
    (v₀ > 0) ->
     ((k0 v₀ a'₀))) ∧
   (∀ (a'₂ : Int),
    ((k0 a'₂ a'₀)) ->
     (a'₂ ≥ 0))
   
end F
