import ExternSpecs.FluxCoreOption00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestAndThenNonePropagates := 
 ∀ (x₀ : Prop),
  ∀ (result₀ : Prop),
   (result₀ -> x₀) ->
    (¬x₀) ->
     ((¬result₀) = True)
end F
