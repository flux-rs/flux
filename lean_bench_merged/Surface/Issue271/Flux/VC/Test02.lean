import Surface.Issue271.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test02 := ∃ k0 : (a0 : Int) -> Prop, 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   (¬(x₀ ≥ 100)) ->
    (((k0 x₀))) ∧
    (((k0 x₀)) ->
     (x₀ < 100))
    
end F
