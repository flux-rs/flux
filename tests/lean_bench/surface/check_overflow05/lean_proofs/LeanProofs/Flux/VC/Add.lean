import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.MAX
open Classical
set_option linter.unusedVariables false


namespace F



def Add := 
 ∀ (x₀ : Int),
  ∀ (y₀ : Int),
   ((x₀ + y₀) ≤ MAX) ->
    (x₀ ≥ 0) ->
     (x₀ ≤ 4294967295) ->
      (y₀ ≥ 0) ->
       (y₀ ≤ 4294967295) ->
        (((x₀ + y₀) ≥ 0)) ∧
        (((x₀ + y₀) ≤ 4294967295))
        
end F
