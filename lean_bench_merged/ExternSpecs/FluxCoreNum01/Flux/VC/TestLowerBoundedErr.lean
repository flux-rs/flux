import ExternSpecs.FluxCoreNum01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestLowerBoundedErr := 
 ∀ (x₀ : Int),
  (x₀ < 0) ->
   ((¬(x₀ ≥ 0)) = True)
end F
