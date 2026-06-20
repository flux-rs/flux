import ExternSpecs.FluxCoreResult00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestUnwrapAfterCheck := 
 ∀ (r₀ : Prop),
  (¬r₀) ->
   (r₀ = False)
end F
