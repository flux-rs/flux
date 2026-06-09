import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Bar := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (y₀ : Int),
  (0 ≤ y₀) ->
   ((¬(y₀ > 10)) ->
    ((k0 0 y₀))) ∧
   ((y₀ > 10) ->
    ((k0 1 y₀))) ∧
   (∀ (a'₀ : Int),
    ((k0 a'₀ y₀)) ->
     (((a'₀ ≥ 0) = True)) ∧
     (((y₀ ≥ 0) = True)) ∧
     ((y₀ ≤ (y₀ + a'₀)))
     )
   
end F
