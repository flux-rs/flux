import AbstractRefinements.Test03.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Lt := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (x₀ : Int),
  ∀ (a'₀ : Int),
   (((k0 a'₀ x₀)) ->
    (a'₀ < x₀)) ∧
   ((a'₀ < x₀) ->
    ((k0 a'₀ x₀)))
   
end F
