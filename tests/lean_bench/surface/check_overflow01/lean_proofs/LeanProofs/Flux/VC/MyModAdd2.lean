import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.MyModMAX
open Classical
set_option linter.unusedVariables false


namespace F



def MyModAdd2 := 
 ∀ (x₀ : Int),
  ((x₀ + 2) ≤ my_mod_MAX) ->
   (x₀ ≥ 0) ->
    (x₀ ≤ 4294967295) ->
     (((x₀ + 2) ≥ 0)) ∧
     (((x₀ + 2) ≤ 4294967295))
     
end F
