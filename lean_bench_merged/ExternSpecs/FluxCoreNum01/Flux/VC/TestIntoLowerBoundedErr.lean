import ExternSpecs.FluxCoreNum01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestIntoLowerBoundedErr := 
 ∀ (x₀ : Int),
  (x₀ < 0) ->
   ∀ (r₀ : Prop),
    (r₀ = (x₀ ≥ 0)) ->
     ((¬r₀) = True)
end F
