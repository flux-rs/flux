import Surface.CheckOverflow01.Flux.Prelude
import Surface.CheckOverflow01.Flux.Fun.MyModMAX
open Classical
set_option linter.unusedVariables false


namespace F



def MyModAdd := 
 ∀ (x₀ : Int),
  ∀ (y₀ : Int),
   ((x₀ + y₀) ≤ my_mod_MAX) ->
    (x₀ ≥ 0) ->
     (x₀ ≤ 4294967295) ->
      (y₀ ≥ 0) ->
       (y₀ ≤ 4294967295) ->
        (((x₀ + y₀) ≥ 0)) ∧
        (((x₀ + y₀) ≤ 4294967295))
        
end F
